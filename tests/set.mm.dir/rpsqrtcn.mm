include "csqrt.mm"
include "crp.mm"
include "cres.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "wa.mm"
include "wral.mm"
include "cc.mm"
include "cr.mm"
include "rpssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "wceq.mm"
include "sqrtf.mm"
include "fdm.mm"
include "ax-mp.mm"
include "sseqtr4i.mm"
include "sseli.mm"
include "rpsqrtcl.mm"
include "jca.mm"
include "rgen.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "ffvresb.mm"
include "mpbir.mm"
include "wss.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cioo.mm"
include "ioorp.mm"
include "ioossico.mm"
include "eqsstr3i.mm"
include "resabs1.mm"
include "resqrtcn.mm"
include "rescncf.mm"
include "mp2.mm"
include "eqeltrri.mm"
include "cncffvrn.mm"
include "mp2an.mm"

theorem rpsqrtcn
  let vx: setvar x


  assert |- ( sqrt |` RR+ ) e. ( RR+ -cn-> RR+ )

  proof
    csqrt
    crp
    cres
    #
    crp
    crp
    ccncf
    co
    wcel
    #
    crp
    crp
    @0
    wf
    #
    @2
    vx
    cv
    #
    csqrt
    cdm
    #
    wcel
    #
    @3
    csqrt
    cfv
    crp
    wcel
    #
    wa
    #
    vx
    crp
    wral
    #
    @7
    vx
    crp
    @3
    crp
    wcel
    @5
    @6
    crp
    @4
    @3
    crp
    cc
    @4
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    #
    cc
    cc
    csqrt
    wf
    #
    @4
    cc
    wceq
    sqrtf
    cc
    cc
    csqrt
    fdm
    ax-mp
    sseqtr4i
    sseli
    @3
    rpsqrtcl
    jca
    rgen
    csqrt
    wfun
    #
    @2
    @8
    wb
    @10
    @11
    sqrtf
    cc
    cc
    csqrt
    ffun
    ax-mp
    vx
    crp
    crp
    csqrt
    ffvresb
    ax-mp
    mpbir
    crp
    cc
    wss
    @0
    crp
    cr
    ccncf
    co
    #
    wcel
    @1
    @2
    wb
    @9
    csqrt
    cc0
    cpnf
    cico
    co
    #
    cres
    #
    crp
    cres
    #
    @0
    @12
    crp
    @13
    wss
    #
    @15
    @0
    wceq
    crp
    cc0
    cpnf
    cioo
    co
    @13
    ioorp
    cc0
    cpnf
    ioossico
    eqsstr3i
    #
    csqrt
    crp
    @13
    resabs1
    ax-mp
    @16
    @14
    @13
    cr
    ccncf
    co
    wcel
    @15
    @12
    wcel
    @17
    resqrtcn
    @13
    cr
    crp
    @14
    rescncf
    mp2
    eqeltrri
    crp
    cr
    crp
    @0
    cncffvrn
    mp2an
    mpbir
end
