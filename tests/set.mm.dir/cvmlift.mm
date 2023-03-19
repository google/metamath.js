include "ccvm.mm"
include "co.mm"
include "wcel.mm"
include "cii.mm"
include "ccn.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cuni.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cres.mm"
include "crest.mm"
include "chmeo.mm"
include "cpw.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "cvmscbv.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "cvmliftlem15.mm"

theorem cvmlift
  let cB: class B
  let cC: class C
  let cP: class P
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let cX: class X
  assume cvmlift.1: |- B = U. C

  disjoint C f
  disjoint G f
  disjoint P f
  disjoint F f
  disjoint J f
  disjoint B f
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint C a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b k
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint C b
  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint C c
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d u
  disjoint d v
  disjoint C d
  disjoint f k
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint C k
  disjoint s u
  disjoint s v
  disjoint C s
  disjoint u v
  disjoint C u
  disjoint C v
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint X a
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F k
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint B b
  disjoint B c
  disjoint B d
  assert |- ( ( ( F e. ( C CovMap J ) /\ G e. ( II Cn J ) ) /\ ( P e. B /\ ( F ` P ) = ( G ` 0 ) ) ) -> E! f e. ( II Cn C ) ( ( F o. f ) = G /\ ( f ` 0 ) = P ) )

  proof
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cG
    cii
    cJ
    ccn
    co
    wcel
    #
    wa
    #
    cP
    cB
    wcel
    #
    cP
    cF
    cfv
    cc0
    cG
    cfv
    wceq
    #
    wa
    #
    wa
    vd
    vc
    cB
    cC
    cP
    vk
    cJ
    vs
    cv
    #
    cuni
    cF
    ccnv
    vk
    cv
    #
    cima
    wceq
    vu
    cv
    #
    vv
    cv
    cin
    c0
    wceq
    vv
    @6
    @8
    csn
    cdif
    wral
    cF
    @8
    cres
    cC
    @8
    crest
    co
    cJ
    @7
    crest
    co
    chmeo
    co
    wcel
    wa
    vu
    @6
    wral
    wa
    vs
    cC
    cpw
    c0
    csn
    cdif
    crab
    cmpt
    #
    vf
    va
    cF
    cG
    cJ
    cJ
    cuni
    #
    vb
    vv
    vu
    cC
    @9
    vk
    cF
    cJ
    vs
    va
    vb
    vc
    vd
    @9
    eqid
    cvmscbv
    cvmlift.1
    @10
    eqid
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    simprr
    cvmliftlem15
end
