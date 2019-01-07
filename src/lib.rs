use std::fmt;

use rand::prelude::*;

enum ChildType { Left, Right }

#[derive(Debug)]
pub struct Node {
	pub value: i32,
	pub left_child: Option<Box<Node>>,
	pub right_child: Option<Box<Node>>,
}

pub struct Preorder<'lt> {
	stack: Vec<&'lt Node>,
}
pub struct Postorder<'lt> {
	stack: Vec<&'lt Node>,
}
pub struct Inorder<'lt> {
	stack: Vec<&'lt Node>,
}

impl<'lt> Preorder<'lt> {
	fn new(root: &'lt Node) -> Preorder<'lt> {
		Preorder { stack: vec![root] }
	}

	fn go_up(&mut self) {
		let last_node = self.stack.pop().unwrap();
		if let Some(parent_node_ref) = self.stack.last() {
			let parent_node = *parent_node_ref;
			if let (Some(parent_left_child_box), Some(parent_right_child_box)) = (&parent_node.left_child, &parent_node.right_child) {
				if parent_left_child_box.as_ref() == last_node {
					self.stack.push(&parent_right_child_box);
					return;
				}
			}
			self.go_up();
		}
	}
}

impl<'lt> Iterator for Preorder<'lt> {
	type Item = &'lt Node;
	
	fn next(&mut self) -> Option<Self::Item> {
		if let Some(last_node_ref) = self.stack.last() {
			let last_node = *last_node_ref;
			if let Some(left_child_box) = last_node.left_child.as_ref() {
				self.stack.push(&left_child_box);
			} else if let Some(right_child_box) = last_node.right_child.as_ref() {
				self.stack.push(&right_child_box);
			} else {
				self.go_up();
			}
			Some(last_node)
		} else {
			None
		}
	}
}

impl<'lt> Postorder<'lt> {
	fn new(root: &'lt Node) -> Postorder<'lt> {
		let mut result: Postorder<'lt> = Postorder { stack: Vec::new() };
		result.add_branch(root);
		result
	}

	fn add_branch(&mut self, branch: &'lt Node) {
		self.stack.push(branch);
		let mut node = branch;
		loop {
			if let Some(left_child_box) = &node.left_child {
				self.stack.push(&left_child_box);
				node = &left_child_box;
			} else if let Some(right_child_box) = &node.right_child {
				self.stack.push(&right_child_box);
				node = &right_child_box;
			} else {
				break;
			}
		}
	}

	fn go_up(&mut self, last_node: &'lt Node) {
		if let Some(parent_node_ref) = self.stack.last() {
			let parent_node = *parent_node_ref;
			if let (Some(parent_left_child_box), Some(parent_right_child_box)) = (&parent_node.left_child, &parent_node.right_child) {
				if last_node == parent_left_child_box.as_ref() {
					self.add_branch(&parent_right_child_box);
				}
			}
		}
	}
}

impl<'lt> Iterator for Postorder<'lt> {
	type Item = &'lt Node;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(last_node) = self.stack.pop() {
			self.go_up(last_node);
			Some(last_node)
		}
		else {
			None
		}
	}
}

impl<'lt> Inorder<'lt> {
	fn new(root: &'lt Node) -> Inorder<'lt> {
		let mut result: Inorder<'lt> = Inorder { stack: Vec::new() };
		result.add_branch(root);
		result
	}

	fn add_branch(&mut self, branch: &'lt Node) {
		self.stack.push(branch);
		let mut node = branch;
		while let Some(left_child_box) = &node.left_child {
			self.stack.push(&left_child_box);
			node = &left_child_box;
		}
	}
}

impl<'lt> Iterator for Inorder<'lt> {
	type Item = &'lt Node;

	fn next(&mut self) -> Option<Self::Item> {
		if let Some(last_node) = self.stack.pop() {
			if let Some(right_child) = &last_node.right_child {
				self.add_branch(right_child);
			}
			Some(last_node)
		}
		else {
			None
		}
	}
}

impl Node {
	pub fn new(value: i32) -> Node {
		Node {
			value,
			left_child: None,
			right_child: None
		}
	}
	
	pub fn set_left_child(self: &mut Node, node: Box<Node>) {
		self.left_child = Some(node);
	}
	pub fn set_right_child(self: &mut Node, node: Box<Node>) {
		self.right_child = Some(node);
	}
	pub fn clear_left_child(self: &mut Node) {
		self.left_child = None;
	}
	pub fn clear_right_child(self: &mut Node) {
		self.right_child = None;
	}

	pub fn preorder(&self) -> Preorder {
		Preorder::new(self)
	}
	pub fn postorder(&self) -> Postorder {
		Postorder::new(self)
	}
	pub fn inorder(&self) -> Inorder {
		Inorder::new(self)
	}
	
	pub fn calc_sum(self: &Node) -> i32 {
		let mut result = self.value;
		if let Some(left_child) = &self.left_child {
			result += left_child.calc_sum();
		}
		if let Some(right_child) = &self.right_child {
			result += right_child.calc_sum();
		}
		result
	}

	pub const DEFAULT_EXTENDED_SYNTAX: bool = true;

	pub fn write_to_string(self: &Node, s: &mut String, extended_syntax: bool) {
		if extended_syntax && self.left_child.is_none() && self.right_child.is_none() {
			s.push_str(&self.value.to_string());
		} else {
			s.push('(');
			s.push_str(&self.value.to_string());
			s.push(' ');
			Node::child_to_string(&self.left_child, s, extended_syntax);
			if !extended_syntax || self.right_child.is_some() {
				s.push(' ');
				Node::child_to_string(&self.right_child, s, extended_syntax);
			}
			s.push(')');
		}
	}

	pub fn draw_to_string(self: &Node, s: &mut String) {
		let mut levels: Vec<ChildType> = Vec::new();
		Node::draw_opt_node_to_string(Some(self), s, &mut levels);
	}

	pub fn generate_random(full_percent: u32, max_levels: u32) -> Box<Node> {
		Node::generate_random_node(&mut thread_rng(), full_percent, max_levels)
	}

	fn generate_random_node(rng: &mut ThreadRng, full_percent: u32, max_levels: u32) -> Box<Node> {
		let normal_dist = rand::distributions::Normal::new(50.0, 50.0);
		let val = (normal_dist.sample(rng) + 0.5) as i32;
		let mut node = Box::new(Node::new(val));
		if max_levels > 0 {
			if rng.gen_ratio(full_percent, 100) {
				node.left_child = Some(Node::generate_random_node(rng, full_percent, max_levels - 1));
			}
			if rng.gen_ratio(full_percent, 100) {
				node.right_child = Some(Node::generate_random_node(rng, full_percent, max_levels - 1));
			}
		}
		node
	}

	fn draw_opt_node_to_string(opt_node: Option<&Node>, s: &mut String, levels: &mut Vec<ChildType>) {
		if !levels.is_empty() {
			for level in &levels[..(levels.len() - 1)] {
				match level {
					ChildType::Left => s.push_str("│   "),
					ChildType::Right => s.push_str("    ")
				}
			}
		}

		match levels.last() {
			Some(ChildType::Left) => s.push_str("├── "),
			Some(ChildType::Right) => s.push_str("└── "),
			None => ()
		}

		match opt_node {
			Some(node) => {
				s.push_str(&node.value.to_string());
				s.push('\n');
				if node.left_child.is_some() || node.right_child.is_some() {
					levels.push(ChildType::Left);
					Node::draw_opt_node_to_string(
						if let Some(child) = &node.left_child { Some(&child) } else { None },
						s, levels);
					levels.pop();

					levels.push(ChildType::Right);
					Node::draw_opt_node_to_string(
						if let Some(child) = &node.right_child { Some(&child) } else { None },
						s, levels);
					levels.pop();
				}
			},
			None => s.push_str("_\n")
		}
	}

	fn child_eq(lhs: &Option<Box<Node>>, rhs: &Option<Box<Node>>) -> bool {
		match (lhs, rhs) {
			(Some(lhs), Some(rhs)) => lhs == rhs,
			(None, None) => true,
			_ => false
		}
	}

	fn child_to_string(child: &Option<Box<Node>>, s: &mut String, extended_syntax: bool) {
		match child {
			Some(child) => child.write_to_string(s, extended_syntax),
			None => s.push('_')
		}
	}
}

impl std::cmp::PartialEq for Node {
	fn eq(&self, other: &Node) -> bool {
		self.value == other.value &&
			Node::child_eq(&self.left_child, &other.left_child) &&
			Node::child_eq(&self.right_child, &other.right_child)
	}
}

impl std::cmp::Eq for Node { }

impl fmt::Display for Node {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let mut s = String::new();
		self.write_to_string(&mut s, Node::DEFAULT_EXTENDED_SYNTAX);
		f.write_str(&s)
	}
}

pub mod parser {
	use super::*;
	
	#[derive(PartialEq, Debug)]
	enum Symbol {
		EmptyPlaceholder,
		ParenthesisOpen,
		ParenthesisClose,
	}
	
	#[derive(PartialEq, Debug)]
	enum Token {
		Number(i32),
		Symbol(Symbol),
	}

	#[derive(Debug)]
	pub struct ParseError {
		pub index: usize,
	}

	impl ParseError {
		fn new(index: usize) -> Self {
			ParseError{ index }
		}
	}
	
	fn parse_symbol(s: &[u8], index: usize) -> Result<(Symbol, usize), ParseError> {
		match s.get(index) {
			Some(b'_') => Ok((Symbol::EmptyPlaceholder, index + 1)),
			Some(b'(') => Ok((Symbol::ParenthesisOpen, index + 1)),
			Some(b')') => Ok((Symbol::ParenthesisClose, index + 1)),
			_ => Err(ParseError::new(index)),
		}
	}

	fn parse_number(s: &[u8], index: usize) -> Result<(i32, usize), ParseError> {
		let mut end_index = index;
		if let Some(b'-') = s.get(end_index) {
			end_index += 1;
		}
		while let Some(b'0' ... b'9') = s.get(end_index) {
			end_index += 1;
		}
		match std::str::from_utf8(&s[index..end_index]) {
			Ok(str_s) => {
				match str_s.parse::<i32>() {
					Ok(val) => Ok((val, end_index)),
					Err(_) => Err(ParseError::new(index)),
				}
			},
			Err(_) => Err(ParseError::new(index))
		}
	}
	
	fn is_whitespace(b: u8) -> bool {
		b == 32 || b == 9 || b == 13 || b == 10
	}
	
	fn trim_left(s: &[u8], index: usize) -> usize {
		let mut end_index = index;
		while let Some(ch) = s.get(end_index) {
			if is_whitespace(*ch) {
				end_index += 1;
			} else {
				break;
			}
		}
		end_index
	}
	
	fn parse_token(s: &[u8], index: usize) -> Result<(Token, usize), ParseError> {
		let beg_index = trim_left(s, index);
		if let Ok((symbol, end_index)) = parse_symbol(s, beg_index) {
			 Ok((Token::Symbol(symbol), end_index))
		} else {
			let (value, end_index) = parse_number(s, beg_index)?;
			Ok((Token::Number(value), end_index))
		}
	}
	
	fn parse_opt_node(s: &[u8], index: usize) -> Result<(Option<Box<Node>>, usize), ParseError> {
		if let Ok((node, end_index)) = parse_node(s, index) {
			Ok((Some(node), end_index))
		} else {
			if let (Token::Symbol(Symbol::EmptyPlaceholder), end_index) = parse_token(s, index)? {
				Ok((None, end_index))
			} else {
				Err(ParseError::new(index))
			}
		}
	}

	fn parse_node(s: &[u8], index: usize) -> Result<(Box<Node>, usize), ParseError> {
		match parse_token(s, index)? {
			(Token::Symbol(Symbol::ParenthesisOpen), end_index) => {
				if let (Token::Number(val), end_index) = parse_token(s, end_index)? {
					let mut result_node = Box::new(Node::new(val));
					let mut result_index = end_index;
					// Parse left child (optional).
					if let Ok((left_subnode_option, end_index)) = parse_opt_node(s, result_index) {
						if let Some(left_subnode) = left_subnode_option {
							result_node.set_left_child(left_subnode);
						}
						result_index = end_index;
						// Parse right child (optional).
						if let Ok((right_subnode_option, end_index)) = parse_opt_node(s, result_index) {
							if let Some(right_subnode) = right_subnode_option {
								result_node.set_right_child(right_subnode);
							}
							result_index = end_index;
						}
					}
					// ')' required.
					if let (Token::Symbol(Symbol::ParenthesisClose), end_index) = parse_token(s, result_index)? {
						Ok((result_node, end_index))
					} else {
						Err(ParseError::new(result_index))
					}
				} else {
					Err(ParseError::new(end_index))
				}
			},
			(Token::Number(val), end_index) => Ok((Box::new(Node::new(val)), end_index)),
			_ => Err(ParseError::new(index)),
		}
	}
		
	pub fn parse(s: &str) -> Result<Box<Node>, ParseError> {
		let s_bytes = s.as_bytes();
		parse_node(s_bytes, 0).and_then(|(node_box, end_index)| {
			let end_index = trim_left(s_bytes, end_index);
			if end_index == s.len() {
				Ok(node_box)
			} else {
				Err(ParseError::new(end_index))
			}
		})
	}
	
	#[cfg(test)]
	mod test {
		use super::*;
		
		#[test]
		fn test_basics() {
			let a = parse_symbol(b"", 0);
			assert!(a.is_err());
			
			let b = parse_symbol(b"_", 0).unwrap();
			assert!(b.0 == parser::Symbol::EmptyPlaceholder);
			assert_eq!(b.1, 1);

			let c = parse_symbol(b")abc", 0).unwrap();
			assert!(c.0 == parser::Symbol::ParenthesisClose);
			assert_eq!(c.1, 1);
			
			let d = parse_number(b"124", 0).unwrap();
			assert_eq!(d.0, 124);
			assert_eq!(d.1, 3);

			let e = parse_number(b"1001^^()_)", 0).unwrap();
			assert_eq!(e.0, 1001);
			assert_eq!(e.1, 4);

			assert!(parse_number(b"^^()_)", 0).is_err());
			
			let f = parse_token(b"", 0);
			assert!(f.is_err());
			
			let g = parse_token(b"\n\n777", 0).unwrap();
			match g.0 {
				Token::Number(val) => assert_eq!(val, 777),
				_ => panic!("Invalid.")
			}
			assert_eq!(g.1, 5);

			let h = parse_token(b" _123", 0).unwrap();
			match h.0 {
				Token::Symbol(sym) => assert_eq!(sym, Symbol::EmptyPlaceholder),
				_ => panic!("Invalid.")
			}
			assert_eq!(h.1, 2);
		}
		
		#[test]
		fn test_main() {
			let n1 = parse("\t\t(1 (2 (21 _ _) _) (3 _ (32 __)) )   ").unwrap();
			//println!("{:#?}", n1);
			assert_eq!(n1.value, 1);

			let n2 = &n1.left_child;
			match n2 {
				Some(n2) => assert_eq!(n2.value, 2),
				None => panic!("Foo.")
			}

			assert_eq!(n1.calc_sum(), 59);
		}

		#[test]
		fn test_extended_syntax() {
			{
				let n1 = parse("(1 (2))").unwrap();
				assert_eq!(n1.value, 1);
				assert!(n1.right_child.is_none());
				
				let n2 = n1.left_child.as_ref().unwrap();
				assert_eq!(n2.value, 2);
				assert!(n2.left_child.is_none());
				assert!(n2.right_child.is_none());
				
				assert_eq!(n1, parse("(1 (2 _ _) _)").unwrap());
			}

			{
				let n1 = parse("(1 _ 2)").unwrap();
				assert_eq!(n1.value, 1);
				assert!(n1.left_child.is_none());

				let n2 = &n1.right_child.as_ref().unwrap();
				assert_eq!(n2.value, 2);
				assert!(n2.left_child.is_none() && n2.right_child.is_none());

				assert_eq!(n1, parse("(1 _ (2 _ _))").unwrap());
			}
		}

		#[test]
		fn test_to_string() {
			let n1 = parse("(32 (-125 _ _) (126 _ (1 -2 -3)))").unwrap();
			let s = n1.to_string();
			//println!("{}", s);
			let n2 = parse(&s).unwrap();
			assert_eq!(n1, n2);
		}

		#[test]
		fn test_failed_parsing() {
			// Unknown character.
			let err = parse("12%").unwrap_err();
			assert_eq!(err.index, 2);

			// Unexpected end - node not closed.
			let err = parse("(1 _ ").unwrap_err();
			assert_eq!(err.index, 5);
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	
	#[test]
	fn basic_test() {
		let mut n1 = Node::new(1);
		assert_eq!(n1.value, 1);
		
		// Set child.
		let n2 = Box::new(Node::new(2));
		n1.set_left_child(n2);
		assert_eq!(n1.left_child.as_ref().unwrap().value, 2);
		//assert_eq!(n1.right_child.unwrap().value, 3);
		assert!(n1.right_child.is_none());
		
		// Reset child to new value.
		let n2 = Box::new(Node::new(3));
		n1.set_left_child(n2);
		assert_eq!(n1.left_child.as_ref().unwrap().value, 3);
		
		//println!("Tree: {:#?}", n1);
		
		// Clear child.
		n1.clear_left_child();
		assert!(n1.left_child.is_none());
	}
}
