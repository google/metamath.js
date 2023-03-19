include "clvec.mm"
include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "crab.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3.mm"
include "weq.mm"
include "id.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "cbvralv.mm"
include "sylib.mm"
include "anbi2i.mm"
include "rabbii.mm"
include "simp1r.mm"
include "lbsextlem4.mm"

theorem lbsextg
  let vx: setvar x
  let cC: class C
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume lbsex.j: |- J = ( LBasis ` W )
  assume lbsex.v: |- V = ( Base ` W )
  assume lbsex.n: |- N = ( LSpan ` W )

  disjoint s x
  disjoint C s
  disjoint C x
  disjoint J s
  disjoint N s
  disjoint N x
  disjoint V s
  disjoint W s
  disjoint W x
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint J y
  disjoint N y
  disjoint N z
  disjoint V y
  disjoint V z
  disjoint W y
  assert |- ( ( ( W e. LVec /\ ~P V e. dom card ) /\ C C_ V /\ A. x e. C -. x e. ( N ` ( C \ { x } ) ) ) -> E. s e. J C C_ s )

  proof
    cW
    clvec
    wcel
    #
    cV
    cpw
    #
    ccrd
    cdm
    wcel
    #
    wa
    #
    cC
    cV
    wss
    #
    vx
    cv
    #
    cC
    @5
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cC
    wral
    #
    w3a
    #
    vy
    vz
    cC
    cC
    vz
    cv
    #
    wss
    #
    @5
    @13
    @6
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @13
    wral
    #
    wa
    #
    vz
    @1
    crab
    cJ
    cN
    cV
    cW
    vs
    lbsex.v
    lbsex.j
    lbsex.n
    @0
    @2
    @4
    @11
    simp1l
    @3
    @4
    @11
    simp2
    @12
    @11
    vy
    cv
    #
    cC
    @21
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vy
    cC
    wral
    @3
    @4
    @11
    simp3
    @10
    @26
    vx
    vy
    cC
    vx
    vy
    weq
    #
    @9
    @25
    @27
    @5
    @21
    @8
    @24
    @27
    id
    #
    @27
    @7
    @23
    cN
    @27
    @6
    @22
    cC
    @5
    @21
    sneq
    #
    difeq2d
    fveq2d
    eleq12d
    notbid
    cbvralv
    sylib
    @20
    @14
    @21
    @13
    @22
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vy
    @13
    wral
    #
    wa
    vz
    @1
    @19
    @34
    @14
    @18
    @33
    vx
    vy
    @13
    @27
    @17
    @32
    @27
    @5
    @21
    @16
    @31
    @28
    @27
    @15
    @30
    cN
    @27
    @6
    @22
    @13
    @29
    difeq2d
    fveq2d
    eleq12d
    notbid
    cbvralv
    anbi2i
    rabbii
    @0
    @2
    @4
    @11
    simp1r
    lbsextlem4
end
