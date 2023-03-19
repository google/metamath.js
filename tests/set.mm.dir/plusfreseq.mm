include "c0.mm"
include "crn.mm"
include "wnel.mm"
include "wfun.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cxp.mm"
include "wral.mm"
include "cres.mm"
include "wfn.mm"
include "plusffn.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "a1i.mm"
include "id.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "plusfval.mm"
include "eqcomd.mm"
include "rgen2a.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqeq12d.mm"
include "ralxp.mm"
include "sylibr.mm"
include "cdm.mm"
include "fndm.mm"
include "fveqressseq.mm"
include "syl3anc.mm"

theorem plusfreseq
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cM: class M
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume plusfreseq.1: |- B = ( Base ` M )
  assume plusfreseq.2: |- .+ = ( +g ` M )
  assume plusfreseq.3: |- .+^ = ( +f ` M )


  assert |- ( (/) e/ ran .+^ -> ( .+ |` ( B X. B ) ) = .+^ )

  proof
    c0
    c.pd
    crn
    wnel
    #
    c.pd
    wfun
    #
    @0
    vp
    cv
    #
    c.pl
    cfv
    #
    @2
    c.pd
    cfv
    #
    wceq
    #
    vp
    cB
    cB
    cxp
    #
    wral
    #
    c.pl
    @6
    cres
    c.pd
    wceq
    @1
    @0
    c.pd
    @6
    wfn
    #
    @1
    cB
    c.pd
    cM
    plusfreseq.1
    plusfreseq.3
    plusffn
    #
    @6
    c.pd
    fnfun
    ax-mp
    a1i
    @0
    id
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    @10
    @11
    c.pd
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @7
    @15
    @0
    @14
    vx
    vy
    cB
    @10
    cB
    wcel
    @11
    cB
    wcel
    wa
    @13
    @12
    cB
    c.pl
    c.pd
    cM
    @10
    @11
    plusfreseq.1
    plusfreseq.2
    plusfreseq.3
    plusfval
    eqcomd
    rgen2a
    a1i
    @5
    @14
    vp
    vx
    vy
    cB
    cB
    @2
    @10
    @11
    cop
    #
    wceq
    #
    @3
    @12
    @4
    @13
    @17
    @3
    @16
    c.pl
    cfv
    @12
    @2
    @16
    c.pl
    fveq2
    @10
    @11
    c.pl
    df-ov
    syl6eqr
    @17
    @4
    @16
    c.pd
    cfv
    @13
    @2
    @16
    c.pd
    fveq2
    @10
    @11
    c.pd
    df-ov
    syl6eqr
    eqeq12d
    ralxp
    sylibr
    vp
    c.pl
    c.pd
    @6
    @8
    @6
    c.pd
    cdm
    #
    wceq
    @9
    @8
    @18
    @6
    @6
    c.pd
    fndm
    eqcomd
    ax-mp
    fveqressseq
    syl3anc
end
