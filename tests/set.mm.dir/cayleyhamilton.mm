include "cpl1.mm"
include "cfv.mm"
include "cmat2pmat.mm"
include "co.mm"
include "cmat.mm"
include "cmulr.mm"
include "ccpmat2mat.mm"
include "cur.mm"
include "cmgp.mm"
include "cmg.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "csg.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cbs.mm"
include "eqid.mm"
include "eqeq1.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "cayleyhamilton0.mm"

theorem cayleyhamilton
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vb: setvar b
  let vm: setvar m
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vl: setvar l
  assume cayleyhamilton.a: |- A = ( N Mat R )
  assume cayleyhamilton.b: |- B = ( Base ` A )
  assume cayleyhamilton.0: |- .0. = ( 0g ` A )
  assume cayleyhamilton.c: |- C = ( N CharPlyMat R )
  assume cayleyhamilton.k: |- K = ( coe1 ` ( C ` M ) )
  assume cayleyhamilton.m: |- .* = ( .s ` A )
  assume cayleyhamilton.e: |- .^ = ( .g ` ( mulGrp ` A ) )

  disjoint A n
  disjoint B n
  disjoint C n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint .* n
  disjoint .^ n
  disjoint A b
  disjoint A m
  disjoint A s
  disjoint A x
  disjoint A y
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint B b
  disjoint B m
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint K b
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M m
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint M l
  disjoint b l
  disjoint l n
  disjoint l s
  disjoint l x
  disjoint l y
  disjoint N b
  disjoint N m
  disjoint N s
  disjoint N x
  disjoint N y
  disjoint N l
  disjoint R b
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint R l
  disjoint .0. b
  disjoint .0. s
  disjoint .0. x
  disjoint .0. y
  disjoint .* m
  disjoint .* s
  disjoint .* x
  disjoint .* y
  disjoint .* b
  disjoint .^ b
  disjoint .^ m
  disjoint .^ s
  disjoint .^ x
  disjoint .^ y
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( A gsum ( n e. NN0 |-> ( ( K ` n ) .* ( n .^ M ) ) ) ) = .0. )

  proof
    cA
    cB
    cC
    cR
    cpl1
    cfv
    #
    cR
    cN
    cR
    cmat2pmat
    co
    #
    cN
    @0
    cmat
    co
    #
    cmulr
    cfv
    #
    cN
    cR
    ccpmat2mat
    co
    #
    cA
    cur
    cfv
    #
    vn
    @2
    cmgp
    cfv
    cmg
    cfv
    #
    c.ex
    vl
    cn0
    vl
    cv
    #
    cc0
    wceq
    #
    @2
    c0g
    cfv
    #
    cM
    @1
    cfv
    #
    cc0
    vy
    cv
    #
    cfv
    @1
    cfv
    @3
    co
    @2
    csg
    cfv
    #
    co
    #
    @7
    vx
    cv
    #
    c1
    caddc
    co
    #
    wceq
    #
    @14
    @11
    cfv
    @1
    cfv
    #
    @15
    @7
    clt
    wbr
    #
    @9
    @7
    c1
    cmin
    co
    #
    @11
    cfv
    #
    @1
    cfv
    #
    @10
    @7
    @11
    cfv
    #
    @1
    cfv
    #
    @3
    co
    #
    @12
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cmpt
    c.as
    cK
    cM
    @12
    cN
    @2
    cbs
    cfv
    #
    @2
    c.0
    @9
    vx
    vy
    cayleyhamilton.a
    cayleyhamilton.b
    cayleyhamilton.0
    @5
    eqid
    cayleyhamilton.m
    cayleyhamilton.e
    cayleyhamilton.c
    cayleyhamilton.k
    @0
    eqid
    @2
    eqid
    @3
    eqid
    @12
    eqid
    @9
    eqid
    @29
    eqid
    @6
    eqid
    @1
    eqid
    vl
    vn
    cn0
    @28
    vn
    cv
    #
    cc0
    wceq
    #
    @13
    @30
    @15
    wceq
    #
    @17
    @15
    @30
    clt
    wbr
    #
    @9
    @30
    c1
    cmin
    co
    #
    @11
    cfv
    #
    @1
    cfv
    #
    @10
    @30
    @11
    cfv
    #
    @1
    cfv
    #
    @3
    co
    #
    @12
    co
    #
    cif
    #
    cif
    #
    cif
    @7
    @30
    wceq
    #
    @8
    @31
    @27
    @42
    @13
    @7
    @30
    cc0
    eqeq1
    @43
    @16
    @32
    @26
    @41
    @17
    @7
    @30
    @15
    eqeq1
    @43
    @18
    @33
    @25
    @40
    @9
    @7
    @30
    @15
    clt
    breq2
    @43
    @21
    @36
    @24
    @39
    @12
    @43
    @20
    @35
    @1
    @43
    @19
    @34
    @11
    @7
    @30
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    @43
    @23
    @38
    @10
    @3
    @43
    @22
    @37
    @1
    @7
    @30
    @11
    fveq2
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    ifbieq2d
    ifbieq2d
    cbvmptv
    @4
    eqid
    cayleyhamilton0
end
