include "ckgen.mm"
include "crn.mm"
include "wcel.mm"
include "ctop.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "iskgen2.mm"
include "wal.mm"
include "ctopon.mm"
include "wb.mm"
include "toptopon.mm"
include "elkgen.mm"
include "sylbi.mm"
include "vex.mm"
include "elpw.mm"
include "anbi1i.mm"
include "syl6bbr.mm"
include "imbi1d.mm"
include "impexp.mm"
include "syl6bb.mm"
include "albidv.mm"
include "dfss2.mm"
include "df-ral.mm"
include "3bitr4g.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iskgen3
  let vx: setvar x
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vz: setvar z
  let wph: wff ph
  assume iskgen3.1: |- X = U. J

  disjoint k x
  disjoint J k
  disjoint J x
  disjoint X k
  disjoint k u
  disjoint k z
  disjoint u x
  disjoint u z
  disjoint J u
  disjoint x z
  disjoint J z
  disjoint k ph
  disjoint ph u
  disjoint ph x
  disjoint X z
  assert |- ( J e. ran kGen <-> ( J e. Top /\ A. x e. ~P X ( A. k e. ~P X ( ( J |`t k ) e. Comp -> ( x i^i k ) e. ( J |`t k ) ) -> x e. J ) ) )

  proof
    cJ
    ckgen
    crn
    wcel
    cJ
    ctop
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cJ
    wss
    #
    wa
    @0
    cJ
    vk
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    vx
    cv
    #
    @3
    cin
    @4
    wcel
    wi
    vk
    cX
    cpw
    #
    wral
    #
    @5
    cJ
    wcel
    #
    wi
    #
    vx
    @6
    wral
    #
    wa
    cJ
    iskgen2
    @0
    @2
    @10
    @0
    @5
    @1
    wcel
    #
    @8
    wi
    #
    vx
    wal
    @5
    @6
    wcel
    #
    @9
    wi
    #
    vx
    wal
    @2
    @10
    @0
    @12
    @14
    vx
    @0
    @12
    @13
    @7
    wa
    #
    @8
    wi
    @14
    @0
    @11
    @15
    @8
    @0
    @11
    @5
    cX
    wss
    #
    @7
    wa
    #
    @15
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @11
    @17
    wb
    cJ
    cX
    iskgen3.1
    toptopon
    @5
    vk
    cJ
    cX
    elkgen
    sylbi
    @13
    @16
    @7
    @5
    cX
    vx
    vex
    elpw
    anbi1i
    syl6bbr
    imbi1d
    @13
    @7
    @8
    impexp
    syl6bb
    albidv
    vx
    @1
    cJ
    dfss2
    @9
    vx
    @6
    df-ral
    3bitr4g
    pm5.32i
    bitri
end
