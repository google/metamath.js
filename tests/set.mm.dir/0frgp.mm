include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "cmpt.mm"
include "wral.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "mptresid.mm"
include "c0.mm"
include "ccom.mm"
include "cghm.mm"
include "co.mm"
include "wrmo.mm"
include "wtru.mm"
include "wa.mm"
include "wreu.mm"
include "cgrp.mm"
include "cvv.mm"
include "wf.mm"
include "0ex.mm"
include "frgpgrp.mm"
include "ax-mp.mm"
include "f0.mm"
include "cvrgp.mm"
include "wfn.mm"
include "cefg.mm"
include "eqid.mm"
include "vrgpf.mm"
include "ffn.mm"
include "mp2b.mm"
include "fn0.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "frgpup3.mm"
include "mp3an.mm"
include "reurmo.mm"
include "idghm.mm"
include "tru.mm"
include "pm3.2i.mm"
include "0ghm.mm"
include "mp2an.mm"
include "wb.mm"
include "co02.mm"
include "bitru.mm"
include "a1i.mm"
include "rmoi.mm"
include "fconstmpt.mm"
include "3eqtri.mm"
include "mpteqb.mm"
include "id.mm"
include "mprg.mm"
include "rspec.mm"
include "velsn.mm"
include "sylibr.mm"
include "ssriv.mm"
include "wss.mm"
include "grpidcl.mm"
include "snssi.mm"
include "eqssi.mm"
include "fvex.mm"
include "ensn1.mm"
include "eqbrtri.mm"

theorem 0frgp
  let cB: class B
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  assume 0frgp.g: |- G = ( freeGrp ` (/) )
  assume 0frgp.b: |- B = ( Base ` G )


  assert |- B ~~ 1o

  proof
    cB
    cG
    c0g
    cfv
    #
    csn
    #
    c1o
    cen
    cB
    @1
    vx
    cB
    @1
    vx
    cv
    #
    cB
    wcel
    #
    @2
    @0
    wceq
    #
    @2
    @1
    wcel
    @4
    vx
    cB
    vx
    cB
    @2
    cmpt
    #
    vx
    cB
    @0
    cmpt
    #
    wceq
    #
    @4
    vx
    cB
    wral
    #
    @5
    cid
    cB
    cres
    #
    cB
    @1
    cxp
    #
    @6
    vx
    cB
    mptresid
    vf
    cv
    #
    c0
    ccom
    c0
    wceq
    #
    vf
    cG
    cG
    cghm
    co
    #
    wrmo
    #
    @9
    @13
    wcel
    #
    wtru
    wa
    @10
    @13
    wcel
    #
    wtru
    wa
    @9
    @10
    wceq
    @12
    vf
    @13
    wreu
    #
    @14
    cG
    cgrp
    wcel
    #
    c0
    cvv
    wcel
    #
    c0
    cB
    c0
    wf
    @17
    @19
    @18
    0ex
    cG
    c0
    cvv
    0frgp.g
    frgpgrp
    ax-mp
    #
    0ex
    cB
    f0
    cB
    c0
    vf
    c0
    cG
    cG
    c0
    cvv
    0frgp.g
    0frgp.b
    c0
    cvrgp
    cfv
    #
    c0
    @21
    c0
    wfn
    #
    @21
    c0
    wceq
    @19
    c0
    cB
    @21
    wf
    @22
    0ex
    c0
    cefg
    cfv
    #
    @21
    cG
    c0
    cvv
    cB
    @23
    eqid
    @21
    eqid
    0frgp.g
    0frgp.b
    vrgpf
    c0
    cB
    @21
    ffn
    mp2b
    @21
    fn0
    mpbi
    eqcomi
    frgpup3
    mp3an
    @12
    vf
    @13
    reurmo
    ax-mp
    @15
    wtru
    @18
    @15
    @20
    cB
    cG
    0frgp.b
    idghm
    ax-mp
    tru
    pm3.2i
    @16
    wtru
    @18
    @18
    @16
    @20
    @20
    cB
    cG
    cG
    @0
    @0
    eqid
    #
    0frgp.b
    0ghm
    mp2an
    tru
    pm3.2i
    @12
    wtru
    wtru
    vf
    @13
    @9
    @10
    @12
    wtru
    wb
    #
    @11
    @9
    wceq
    @12
    @11
    co02
    bitru
    #
    a1i
    @25
    @11
    @10
    wceq
    @26
    a1i
    rmoi
    mp3an
    vx
    cB
    @0
    fconstmpt
    3eqtri
    @3
    @7
    @8
    wb
    vx
    cB
    vx
    cB
    @2
    @0
    cB
    mpteqb
    @3
    id
    mprg
    mpbi
    rspec
    vx
    @0
    velsn
    sylibr
    ssriv
    @0
    cB
    wcel
    #
    @1
    cB
    wss
    @18
    @27
    @20
    cB
    cG
    @0
    0frgp.b
    @24
    grpidcl
    ax-mp
    @0
    cB
    snssi
    ax-mp
    eqssi
    @0
    cG
    c0g
    fvex
    ensn1
    eqbrtri
end
