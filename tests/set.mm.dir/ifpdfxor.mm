include "wxo.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wtru.mm"
include "wif.mm"
include "wfal.mm"
include "xor2.mm"
include "ifpdfor.mm"
include "ifpnot23.mm"
include "ifpdfan.mm"
include "xchnxbir.mm"
include "anbi12i.mm"
include "ifpan23.mm"
include "wb.mm"
include "truan.mm"
include "fal.mm"
include "biantru.mm"
include "bicomi.mm"
include "ifpbi23.mm"
include "mp2an.mm"
include "bitri.mm"
include "3bitri.mm"

theorem ifpdfxor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) <-> if- ( ph , -. ps , ps ) )

  proof
    wph
    wps
    wxo
    wph
    wps
    wo
    #
    wph
    wps
    wa
    #
    wn
    #
    wa
    wph
    wtru
    wps
    wif
    #
    wph
    wps
    wn
    #
    wfal
    wn
    #
    wif
    #
    wa
    #
    wph
    @4
    wps
    wif
    #
    wph
    wps
    xor2
    @0
    @3
    @2
    @6
    wph
    wps
    ifpdfor
    wph
    wps
    wfal
    wif
    @6
    @1
    wph
    wps
    wfal
    ifpnot23
    wph
    wps
    ifpdfan
    xchnxbir
    anbi12i
    @7
    wph
    wtru
    @4
    wa
    #
    wps
    @5
    wa
    #
    wif
    #
    @8
    wph
    wtru
    wps
    @4
    @5
    ifpan23
    @9
    @4
    wb
    @10
    wps
    wb
    @11
    @8
    wb
    @4
    truan
    wps
    @10
    @5
    wps
    fal
    biantru
    bicomi
    @9
    @4
    @10
    wps
    wph
    ifpbi23
    mp2an
    bitri
    3bitri
end
