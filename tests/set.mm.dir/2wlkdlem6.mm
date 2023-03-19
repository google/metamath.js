include "cpr.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "wcel.mm"
include "prcom.mm"
include "sseq1i.mm"
include "biimpi.mm"
include "adantl.mm"
include "wb.mm"
include "simp2d.mm"
include "simp1d.mm"
include "adantr.mm"
include "prssg.mm"
include "syl2an2r.mm"
include "mpbird.mm"
include "simpld.mm"
include "ex.mm"
include "simpr.mm"
include "simp3d.mm"
include "anim12d.mm"
include "mpd.mm"

theorem 2wlkdlem6
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let vk: setvar k
  let vj: setvar j
  assume 2wlkd.p: |- P = <" A B C ">
  assume 2wlkd.f: |- F = <" J K ">
  assume 2wlkd.s: |- ( ph -> ( A e. V /\ B e. V /\ C e. V ) )
  assume 2wlkd.n: |- ( ph -> ( A =/= B /\ B =/= C ) )
  assume 2wlkd.e: |- ( ph -> ( { A , B } C_ ( I ` J ) /\ { B , C } C_ ( I ` K ) ) )


  assert |- ( ph -> ( B e. ( I ` J ) /\ B e. ( I ` K ) ) )

  proof
    wph
    cA
    cB
    cpr
    #
    cJ
    cI
    cfv
    #
    wss
    #
    cB
    cC
    cpr
    cK
    cI
    cfv
    #
    wss
    #
    wa
    cB
    @1
    wcel
    #
    cB
    @3
    wcel
    #
    wa
    2wlkd.e
    wph
    @2
    @5
    @4
    @6
    wph
    @2
    @5
    wph
    @2
    wa
    #
    @5
    cA
    @1
    wcel
    #
    @7
    @5
    @8
    wa
    #
    cB
    cA
    cpr
    #
    @1
    wss
    #
    @2
    @11
    wph
    @2
    @11
    @0
    @10
    @1
    cA
    cB
    prcom
    sseq1i
    biimpi
    adantl
    wph
    cB
    cV
    wcel
    #
    @2
    cA
    cV
    wcel
    #
    @9
    @11
    wb
    wph
    @13
    @12
    cC
    cV
    wcel
    #
    2wlkd.s
    simp2d
    #
    wph
    @13
    @2
    wph
    @13
    @12
    @14
    2wlkd.s
    simp1d
    adantr
    cB
    cA
    @1
    cV
    cV
    prssg
    syl2an2r
    mpbird
    simpld
    ex
    wph
    @4
    @6
    wph
    @4
    wa
    #
    @6
    cC
    @3
    wcel
    #
    @16
    @6
    @17
    wa
    #
    @4
    wph
    @4
    simpr
    wph
    @12
    @4
    @14
    @18
    @4
    wb
    @15
    wph
    @14
    @4
    wph
    @13
    @12
    @14
    2wlkd.s
    simp3d
    adantr
    cB
    cC
    @3
    cV
    cV
    prssg
    syl2an2r
    mpbird
    simpld
    ex
    anim12d
    mpd
end
