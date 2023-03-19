include "c0.mm"
include "cibl.mm"
include "wcel.mm"
include "cmbf.mm"
include "cr.mm"
include "cc0.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "wral.mm"
include "mbf0.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "itg20.mm"
include "eqtri.mm"
include "0re.mm"
include "eqeltri.mm"
include "rgenw.mm"
include "wa.mm"
include "wb.mm"
include "wtru.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "noel.mm"
include "intnanr.mm"
include "iffalsei.mm"
include "a1i.mm"
include "mpteq2dva.mm"
include "eqidd.mm"
include "cdm.mm"
include "dm0.mm"
include "intnan.mm"
include "pm2.21i.mm"
include "isibl.mm"
include "trud.mm"
include "mpbir2an.mm"

theorem iblempty
  let vk: setvar k
  let vx: setvar x


  assert |- (/) e. L^1

  proof
    c0
    cibl
    wcel
    #
    c0
    cmbf
    wcel
    #
    vx
    cr
    cc0
    cmpt
    #
    citg2
    cfv
    #
    cr
    wcel
    #
    vk
    cc0
    c3
    cfz
    co
    #
    wral
    #
    mbf0
    @4
    vk
    @5
    @3
    cc0
    cr
    @3
    cr
    cc0
    csn
    cxp
    #
    citg2
    cfv
    cc0
    @2
    @7
    citg2
    @7
    @2
    vx
    cr
    cc0
    fconstmpt
    eqcomi
    fveq2i
    itg20
    eqtri
    0re
    eqeltri
    rgenw
    @0
    @1
    @6
    wa
    wb
    wtru
    vx
    c0
    cc0
    cc0
    ci
    vk
    cv
    cexp
    co
    cdiv
    co
    cre
    cfv
    #
    vk
    c0
    @2
    wtru
    vx
    cr
    cc0
    vx
    cv
    #
    c0
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    wa
    #
    @8
    cc0
    cif
    #
    cc0
    @13
    wceq
    wtru
    @9
    cr
    wcel
    wa
    @13
    cc0
    @12
    @8
    cc0
    @10
    @11
    @9
    noel
    #
    intnanr
    iffalsei
    eqcomi
    a1i
    mpteq2dva
    wtru
    @10
    wa
    #
    @8
    eqidd
    c0
    cdm
    c0
    wceq
    wtru
    dm0
    a1i
    @15
    @9
    c0
    cfv
    cc0
    wceq
    @10
    wtru
    @14
    intnan
    pm2.21i
    isibl
    trud
    mpbir2an
end
