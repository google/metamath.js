include "cv.mm"
include "wcel.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "simpl.mm"
include "simpr.mm"
include "wb.mm"
include "cpsmet.mm"
include "cxr.mm"
include "elblps.mm"
include "syl3anc.mm"
include "adantr.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "ex.mm"
include "ralrimi.mm"
include "dfss3.mm"
include "sylibr.mm"

theorem ballss3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  assume ballss3.y: |- F/ x ph
  assume ballss3.d: |- ( ph -> D e. ( PsMet ` X ) )
  assume ballss3.p: |- ( ph -> P e. X )
  assume ballss3.r: |- ( ph -> R e. RR* )
  assume ballss3.a: |- ( ( ph /\ x e. X /\ ( P D x ) < R ) -> x e. A )

  disjoint A x
  disjoint D x
  disjoint P x
  disjoint R x
  assert |- ( ph -> ( P ( ball ` D ) R ) C_ A )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vx
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    wral
    @2
    cA
    wss
    wph
    @1
    vx
    @2
    ballss3.y
    wph
    @0
    @2
    wcel
    #
    @1
    wph
    @3
    wa
    #
    wph
    @0
    cX
    wcel
    #
    cP
    @0
    cD
    co
    cR
    clt
    wbr
    #
    @1
    wph
    @3
    simpl
    @4
    @5
    @6
    @4
    @3
    @5
    @6
    wa
    #
    wph
    @3
    simpr
    wph
    @3
    @7
    wb
    #
    @3
    wph
    cD
    cX
    cpsmet
    cfv
    wcel
    cP
    cX
    wcel
    cR
    cxr
    wcel
    @8
    ballss3.d
    ballss3.p
    ballss3.r
    @0
    cD
    cP
    cR
    cX
    elblps
    syl3anc
    adantr
    mpbid
    #
    simpld
    @4
    @5
    @6
    @9
    simprd
    ballss3.a
    syl3anc
    ex
    ralrimi
    vx
    @2
    cA
    dfss3
    sylibr
end
