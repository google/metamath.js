include "csin.mm"
include "cr.mm"
include "cres.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cc.mm"
include "wss.mm"
include "sinf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ax-resscn.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fvres.mm"
include "resincl.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wb.mm"
include "sincn.mm"
include "rescncf.mm"
include "mp2.mm"
include "cncffvrn.mm"
include "mpbir.mm"

theorem resincncf
  let vk: setvar k
  let vx: setvar x


  assert |- ( sin |` RR ) e. ( RR -cn-> RR )

  proof
    csin
    cr
    cres
    #
    cr
    cr
    ccncf
    co
    wcel
    #
    cr
    cr
    @0
    wf
    #
    @2
    @0
    cr
    wfn
    #
    vx
    cv
    #
    @0
    cfv
    #
    cr
    wcel
    #
    vx
    cr
    wral
    csin
    cc
    wfn
    #
    cr
    cc
    wss
    #
    @3
    cc
    cc
    csin
    wf
    @7
    sinf
    cc
    cc
    csin
    ffn
    ax-mp
    ax-resscn
    cc
    cr
    csin
    fnssres
    mp2an
    @6
    vx
    cr
    @4
    cr
    wcel
    @5
    @4
    csin
    cfv
    cr
    @4
    cr
    csin
    fvres
    @4
    resincl
    eqeltrd
    rgen
    vx
    cr
    cr
    @0
    ffnfv
    mpbir2an
    @8
    @0
    cr
    cc
    ccncf
    co
    wcel
    #
    @1
    @2
    wb
    ax-resscn
    @8
    csin
    cc
    cc
    ccncf
    co
    wcel
    @9
    ax-resscn
    sincn
    cc
    cc
    cr
    csin
    rescncf
    mp2
    cr
    cc
    cr
    @0
    cncffvrn
    mp2an
    mpbir
end
