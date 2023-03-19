include "cdic.mm"
include "cfv.mm"
include "cdvh.mm"
include "cplusg.mm"
include "clsm.mm"
include "cdib.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "clss.mm"
include "cid.mm"
include "cres.mm"
include "eqid.mm"
include "dihopelvalcpre.mm"

theorem dihopelvalc
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cC: class C
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vh: setvar h
  let cN: class N
  let cZ: class Z
  assume dihopelvalcp.b: |- B = ( Base ` K )
  assume dihopelvalcp.l: |- .<_ = ( le ` K )
  assume dihopelvalcp.j: |- .\/ = ( join ` K )
  assume dihopelvalcp.m: |- ./\ = ( meet ` K )
  assume dihopelvalcp.a: |- A = ( Atoms ` K )
  assume dihopelvalcp.h: |- H = ( LHyp ` K )
  assume dihopelvalcp.p: |- P = ( ( oc ` K ) ` W )
  assume dihopelvalcp.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihopelvalcp.r: |- R = ( ( trL ` K ) ` W )
  assume dihopelvalcp.e: |- E = ( ( TEndo ` K ) ` W )
  assume dihopelvalcp.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihopelvalcp.g: |- G = ( iota_ g e. T ( g ` P ) = Q )
  assume dihopelvalcp.f: |- F e. _V
  assume dihopelvalcp.s: |- S e. _V

  disjoint .<_ g
  disjoint A g
  disjoint P g
  disjoint H g
  disjoint K g
  disjoint T g
  disjoint W g
  disjoint Q g
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .\/ w
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .<_ w
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ w
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V x
  disjoint V y
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint E a
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint E b
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint g h
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint H h
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint a g
  disjoint a h
  disjoint K a
  disjoint b g
  disjoint b h
  disjoint K b
  disjoint K h
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint B h
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint T a
  disjoint T b
  disjoint T h
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint W a
  disjoint W b
  disjoint W h
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( Q .\/ ( X ./\ W ) ) = X ) ) -> ( <. F , S >. e. ( I ` X ) <-> ( ( F e. T /\ S e. E ) /\ ( R ` ( F o. `' ( S ` G ) ) ) .<_ X ) ) )

  proof
    cA
    cB
    cW
    cK
    cdic
    cfv
    cfv
    #
    cP
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cplusg
    cfv
    #
    @1
    clsm
    cfv
    #
    cQ
    cR
    cS
    cT
    @1
    vg
    vh
    cE
    cF
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cK
    cdib
    cfv
    cfv
    #
    va
    vb
    cE
    cE
    vh
    cT
    vh
    cv
    #
    va
    cv
    cfv
    @5
    vb
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    @1
    clss
    cfv
    #
    cW
    cX
    vh
    cT
    cid
    cB
    cres
    cmpt
    #
    va
    vb
    dihopelvalcp.b
    dihopelvalcp.l
    dihopelvalcp.j
    dihopelvalcp.m
    dihopelvalcp.a
    dihopelvalcp.h
    dihopelvalcp.p
    dihopelvalcp.t
    dihopelvalcp.r
    dihopelvalcp.e
    dihopelvalcp.i
    dihopelvalcp.g
    dihopelvalcp.f
    dihopelvalcp.s
    @8
    eqid
    @4
    eqid
    @0
    eqid
    @1
    eqid
    @2
    eqid
    @7
    eqid
    @3
    eqid
    @6
    eqid
    dihopelvalcpre
end
