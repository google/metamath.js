include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "crg.mm"
include "ccom.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmulr.mm"
include "crngring.mm"
include "3ad2ant1.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "zrhcopsgnelbas.mm"
include "syl3anc.mm"
include "eqid.mm"
include "mgpbas.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "wral.mm"
include "simp2.mm"
include "matepm2cl.mm"
include "gsummptcl.mm"
include "ringcl.mm"

theorem madetsmelbas2
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cN: class N
  let cY: class Y
  assume madetsmelbas.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume madetsmelbas.s: |- S = ( pmSgn ` N )
  assume madetsmelbas.y: |- Y = ( ZRHom ` R )
  assume madetsmelbas.a: |- A = ( N Mat R )
  assume madetsmelbas.b: |- B = ( Base ` A )
  assume madetsmelbas.g: |- G = ( mulGrp ` R )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint Q n
  disjoint R n
  assert |- ( ( R e. CRing /\ M e. B /\ Q e. P ) -> ( ( ( Y o. S ) ` Q ) ( .r ` R ) ( G gsum ( n e. N |-> ( n M ( Q ` n ) ) ) ) ) e. ( Base ` R ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    cQ
    cP
    wcel
    #
    w3a
    #
    cR
    crg
    wcel
    #
    cQ
    cY
    cS
    ccom
    cfv
    #
    cR
    cbs
    cfv
    #
    wcel
    #
    cG
    vn
    cN
    vn
    cv
    #
    @8
    cQ
    cfv
    cM
    co
    #
    cmpt
    cgsu
    co
    #
    @6
    wcel
    @5
    @10
    cR
    cmulr
    cfv
    #
    co
    @6
    wcel
    @0
    @1
    @4
    @2
    cR
    crngring
    3ad2ant1
    #
    @3
    @4
    cN
    cfn
    wcel
    #
    @2
    @7
    @12
    @1
    @0
    @13
    @2
    @1
    @13
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cM
    madetsmelbas.a
    madetsmelbas.b
    matrcl
    simpld
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    #
    cP
    cQ
    cR
    cS
    cN
    cY
    madetsmelbas.p
    madetsmelbas.s
    madetsmelbas.y
    zrhcopsgnelbas
    syl3anc
    @3
    @6
    vn
    cG
    cN
    @9
    @6
    cR
    cG
    madetsmelbas.g
    @6
    eqid
    #
    mgpbas
    @0
    @1
    cG
    ccmn
    wcel
    @2
    cR
    cG
    madetsmelbas.g
    crngmgp
    3ad2ant1
    @14
    @3
    @4
    @2
    @1
    @9
    @6
    wcel
    vn
    cN
    wral
    @12
    @15
    @0
    @1
    @2
    simp2
    cA
    cB
    cP
    cQ
    cR
    vn
    cM
    cN
    madetsmelbas.a
    madetsmelbas.b
    madetsmelbas.p
    matepm2cl
    syl3anc
    gsummptcl
    @6
    cR
    @11
    @5
    @10
    @16
    @11
    eqid
    ringcl
    syl3anc
end
