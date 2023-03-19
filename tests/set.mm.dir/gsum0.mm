include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "cv.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "eqid.mm"
include "id.mm"
include "0ex.mm"
include "a1i.mm"
include "wf.mm"
include "f0.mm"
include "gsumval1.mm"
include "wn.mm"
include "crn.mm"
include "wss.mm"
include "c0g.mm"
include "cdm.mm"
include "cfz.mm"
include "cseq.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "ccnv.mm"
include "cdif.mm"
include "cima.mm"
include "wsbc.mm"
include "cif.mm"
include "csb.mm"
include "df-gsum.mm"
include "reldmmpt2.mm"
include "ovprc1.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem gsum0
  let cG: class G
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume gsum0.z: |- .0. = ( 0g ` G )


  assert |- ( G gsum (/) ) = .0.

  proof
    cG
    cvv
    wcel
    #
    cG
    c0
    cgsu
    co
    #
    c.0
    wceq
    @0
    vx
    vy
    c0
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    c0
    cG
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    @5
    wceq
    @5
    @4
    @3
    co
    @5
    wceq
    wa
    vy
    @2
    wral
    vx
    @2
    crab
    #
    cvv
    cvv
    c.0
    @2
    eqid
    gsum0.z
    @3
    eqid
    @6
    eqid
    @0
    id
    c0
    cvv
    wcel
    @0
    0ex
    a1i
    c0
    @6
    c0
    wf
    @0
    @6
    f0
    a1i
    gsumval1
    @0
    wn
    #
    @1
    c0
    c.0
    cG
    c0
    cgsu
    vw
    vf
    cvv
    cvv
    vo
    @4
    @5
    vw
    cv
    #
    cplusg
    cfv
    #
    co
    @5
    wceq
    @5
    @4
    @9
    co
    @5
    wceq
    wa
    vy
    @8
    cbs
    cfv
    #
    wral
    vx
    @10
    crab
    vf
    cv
    #
    crn
    vo
    cv
    #
    wss
    @8
    c0g
    cfv
    @11
    cdm
    #
    cfz
    crn
    wcel
    @13
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    wceq
    @4
    @15
    @9
    @11
    @14
    cseq
    cfv
    wceq
    wa
    vn
    @14
    cuz
    cfv
    wrex
    vm
    wex
    vx
    cio
    c1
    @5
    chash
    cfv
    #
    cfz
    co
    @5
    vg
    cv
    #
    wf1o
    @4
    @16
    @9
    @11
    @17
    ccom
    c1
    cseq
    cfv
    wceq
    wa
    vy
    @11
    ccnv
    cvv
    @12
    cdif
    cima
    wsbc
    vg
    wex
    vx
    cio
    cif
    cif
    csb
    cgsu
    vx
    vy
    vw
    vf
    vg
    vm
    vn
    vo
    df-gsum
    reldmmpt2
    ovprc1
    @7
    c.0
    cG
    c0g
    cfv
    c0
    gsum0.z
    cG
    c0g
    fvprc
    syl5eq
    eqtr4d
    pm2.61i
end
