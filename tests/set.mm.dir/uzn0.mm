include "cuz.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "uzf.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "mp2b.mm"
include "uzid.mm"
include "ne0i.mm"
include "syl.mm"
include "neeq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"

theorem uzn0
  let cM: class M
  let vk: setvar k


  assert |- ( M e. ran ZZ>= -> M =/= (/) )

  proof
    cM
    cuz
    crn
    wcel
    #
    vk
    cv
    #
    cuz
    cfv
    #
    cM
    wceq
    #
    vk
    cz
    wrex
    #
    cM
    c0
    wne
    #
    cz
    cz
    cpw
    #
    cuz
    wf
    cuz
    cz
    wfn
    @0
    @4
    wb
    uzf
    cz
    @6
    cuz
    ffn
    vk
    cz
    cM
    cuz
    fvelrnb
    mp2b
    @3
    @5
    vk
    cz
    @1
    cz
    wcel
    #
    @2
    c0
    wne
    #
    @3
    @5
    @7
    @1
    @2
    wcel
    @8
    @1
    uzid
    @2
    @1
    ne0i
    syl
    @2
    cM
    c0
    neeq1
    syl5ibcom
    rexlimiv
    sylbi
end
