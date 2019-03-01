package tree

// DeclareCursor represents an `DECLARE CURSOR <foo> FOR <stmt>` statement.
type DeclareCursor struct {
	Name string
	Stmt SelectStatement
}

// Format implements the NodeFormatter interface.
func (n *DeclareCursor) Format(ctx *FmtCtx) {
	ctx.WriteString("DECLARE CURSOR ")
	ctx.WriteString(n.Name)
	ctx.WriteString(" FOR ")
	ctx.FormatNode(n.Stmt)
}

func (n *DeclareCursor) StatementType() StatementType { return Ack }
func (n *DeclareCursor) StatementTag() string         { return "DECLARE" }
func (n *DeclareCursor) String() string {
	return AsString(n)
}

type FetchCursor struct {
	Name string
}

// Format implements the NodeFormatter interface.
func (n *FetchCursor) Format(ctx *FmtCtx) {
	ctx.WriteString("FETCH ")
	ctx.WriteString(n.Name)
}

func (n *FetchCursor) StatementType() StatementType { return Rows }
func (n *FetchCursor) StatementTag() string         { return "FETCH" }
func (n *FetchCursor) String() string {
	return AsString(n)
}
