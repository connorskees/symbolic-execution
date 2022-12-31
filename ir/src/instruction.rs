use iced_x86::Register;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InstructionIdx(pub u32);

#[derive(Debug)]
pub struct Instruction {
    operands: Operands,
    kind: InstructionKind,
}

impl Instruction {
    pub fn new(kind: InstructionKind, operands: Operands) -> Self {
        Self { operands, kind }
    }
}

#[derive(Debug)]
pub struct Operands([Operand; 3]);

impl Operands {
    pub fn one(op: Operand) -> Self {
        Self([op, Operand::None, Operand::None])
    }

    pub fn two(op1: Operand, op2: Operand) -> Self {
        Self([op1, op2, Operand::None])
    }

    pub fn three(op1: Operand, op2: Operand, op3: Operand) -> Self {
        Self([op1, op2, op3])
    }
}

pub struct MemoryAccess {}

#[derive(Debug, Clone, Copy)]
pub enum Operand {
    Instruction(InstructionIdx),
    Register(Register),
    Memory(u32),
    Imm(u64, u32),
    None,
}

impl Operand {
    pub fn get_bit_size(&self) -> u32 {
        todo!()
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstructionKind {
    /// Invalid node.
    Invalid = 0,

    /// BVADDx y)
    BvAdd = 5,

    /// (bvand x y)
    BvAnd = 7,

    /// (bvashr x y)
    BVASHR = 12,

    /// (bvlshr x y)
    BVLSHR = 17,

    /// (bvmul x y)
    BvMul = 19,

    /// (bvnand x y)
    BVNAND = 23,

    /// (bvneg x)
    BVNEG = 29,

    /// (bvnor x y)
    BVNOR = 31,

    /// (bvnot x)
    BVNOT = 37,

    ///  (bvor x y)
    BVOR = 41,

    /// ((_ rotate_left x) y)
    BVROL = 43,

    /// ((_ rotate_right x) y)
    BVROR = 47,

    /// (bvsdiv x y)
    BVSDIV = 53,

    /// (bvsge x y)
    BVSGE = 59,

    ///  (bvsgt x y)
    BVSGT = 61,

    /// (bvshl x y)
    BVSHL = 67,

    /// (bvsle x y)
    BVSLE = 71,

    /// (bvslt x y)
    BVSLT = 73,

    /// (bvsmod x y)
    BVSMOD = 79,

    /// (bvsrem x y)
    BVSREM = 83,

    /// (bvsub x y)
    BvSub = 89,

    /// (bvudiv x y)
    BVUDIV = 97,

    /// (bvuge x y)
    BVUGE = 101,

    /// (bvugt x y)
    BvUgt = 103,

    /// (bvule x y)
    BVULE = 107,

    /// (bvult x y)
    BVULT = 109,

    /// (bvurem x y)
    BVUREM = 113,

    /// (bvxnor x y)
    BVXNOR = 127,

    /// (bvxor x y)
    BvXor = 131,

    /// (_ bvx y)
    Bv = 137,

    /// A compound of nodes
    COMPOUND = 139,

    /// (concat x y z ...)
    CONCAT = 149,

    /// (declare-fun <var_name> () (_ BitVec <var_size>))
    DECLARE = 151,

    /// (distinct x y)
    DISTINCT = 157,

    /// (= x y)
    Equal = 163,

    /// ((_ extract x y) z)
    Extract = 167,

    /// (forall ((x (_ BitVec <size>)), ...) body)
    FORALL = 173,

    /// (iff x y)
    IFF = 179,

    /// Integer node
    INTEGER = 181,

    /// (ite x y z)
    ITE = 191,

    /// (and x y)
    LAND = 193,

    /// (let ((x y)) z)
    LET = 197,

    /// (and x y)
    LNOT = 199,

    /// (or x y)
    LOR = 211,

    /// (xor x y)
    LXOR = 223,

    /// Reference node
    REFERENCE = 227,

    /// String node
    STRING = 229,

    /// ((_ sign_extend x) y)
    SX = 233,

    /// ((_ zero_extend x) y)
    Zx = 241,

    /// Undefined value
    UNDEF = 242,

    /// Memory address
    Memory = 243,

    /// Register
    REGISTER = 244,

    /// Temporary variable
    TEMPVAR = 245,

    /// SSA version of a variable node
    SSAVAR = 246,

    ZERO = 247,
    CARRY = 248,
    OVERFLOW = 249,
    SIGN = 250,
    PARITY = 251,
}
