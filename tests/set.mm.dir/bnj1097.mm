include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wss.mm"
include "wcel.mm"
include "wfn.mm"
include "biimpi.mm"
include "bnj771.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "cvv.mm"
include "w-bnj19.mm"
include "simp3bi.mm"
include "3ad2ant2.mm"
include "jca.mm"
include "anim2i.mm"
include "3anass.mm"
include "sylibr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "biimpar.mm"
include "simpr.mm"
include "eqsstrd.mm"
include "3impa.mm"
include "syl.mm"

theorem bnj1097
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let bnjwph0: wff ph0
  assume bnj1097.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1097.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1097.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )


  assert |- ( ( i = (/) /\ ( ( th /\ ta /\ ch ) /\ ph0 ) ) -> ( f ` i ) C_ B )

  proof
    vi
    cv
    #
    c0
    wceq
    #
    wth
    wta
    wch
    w3a
    #
    bnjwph0
    wa
    #
    wa
    #
    @1
    c0
    vf
    cv
    #
    cfv
    #
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    @7
    cB
    wss
    #
    w3a
    #
    @0
    @5
    cfv
    #
    cB
    wss
    #
    @4
    @1
    @8
    @9
    wa
    #
    wa
    @10
    @3
    @13
    @1
    @3
    @8
    @9
    @2
    @8
    bnjwph0
    wch
    wth
    @8
    wta
    vn
    cv
    #
    cD
    wcel
    @5
    @14
    wfn
    wph
    wps
    @8
    wch
    bnj1097.3
    wph
    @8
    bnj1097.1
    biimpi
    bnj771
    3ad2ant3
    adantr
    @2
    @9
    bnjwph0
    wta
    wth
    @9
    wch
    wta
    cB
    cvv
    wcel
    cA
    cB
    cR
    w-bnj19
    @9
    bnj1097.5
    simp3bi
    3ad2ant2
    adantr
    jca
    anim2i
    @1
    @8
    @9
    3anass
    sylibr
    @1
    @8
    @9
    @12
    @1
    @8
    wa
    #
    @9
    wa
    @11
    @7
    cB
    @15
    @11
    @7
    wceq
    #
    @9
    @1
    @16
    @8
    @1
    @11
    @6
    @7
    @0
    c0
    @5
    fveq2
    eqeq1d
    biimpar
    adantr
    @15
    @9
    simpr
    eqsstrd
    3impa
    syl
end
