include "crefld.mm"
include "csr.mm"
include "wcel.mm"
include "wtru.mm"
include "cr.mm"
include "ccj.mm"
include "rebase.mm"
include "refldcj.mm"
include "ccrg.mm"
include "cdr.mm"
include "cfield.mm"
include "wa.mm"
include "refld.mm"
include "isfld.mm"
include "mpbi.mm"
include "simpri.mm"
include "a1i.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cjre.mm"
include "adantl.mm"
include "idsrngd.mm"
include "trud.mm"

theorem recrng
  let vx: setvar x


  assert |- RRfld e. *Ring

  proof
    crefld
    csr
    wcel
    wtru
    vx
    cr
    crefld
    ccj
    rebase
    refldcj
    crefld
    ccrg
    wcel
    #
    wtru
    crefld
    cdr
    wcel
    #
    @0
    crefld
    cfield
    wcel
    @1
    @0
    wa
    refld
    crefld
    isfld
    mpbi
    simpri
    a1i
    vx
    cv
    #
    cr
    wcel
    @2
    ccj
    cfv
    @2
    wceq
    wtru
    @2
    cjre
    adantl
    idsrngd
    trud
end
