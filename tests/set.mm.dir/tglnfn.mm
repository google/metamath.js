include "cstrkg.mm"
include "wcel.mm"
include "cxp.mm"
include "cid.mm"
include "cdif.mm"
include "wfn.mm"
include "cv.mm"
include "csn.mm"
include "co.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "ciun.mm"
include "cvv.mm"
include "wf.mm"
include "wral.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "rgen2w.mm"
include "eqid.mm"
include "fmpt2x.mm"
include "mpbi.mm"
include "ffn.mm"
include "ax-mp.mm"
include "xpdifid.mm"
include "fneq2i.mm"
include "tglng.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem tglnfn
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglng.p: |- P = ( Base ` G )
  assume tglng.l: |- L = ( LineG ` G )
  assume tglng.i: |- I = ( Itv ` G )


  assert |- ( G e. TarskiG -> L Fn ( ( P X. P ) \ _I ) )

  proof
    cG
    cstrkg
    wcel
    #
    cL
    cP
    cP
    cxp
    cid
    cdif
    #
    wfn
    vx
    vy
    cP
    cP
    vx
    cv
    #
    csn
    #
    cdif
    #
    vz
    cv
    #
    @2
    vy
    cv
    #
    cI
    co
    wcel
    @2
    @5
    @6
    cI
    co
    wcel
    @6
    @2
    @5
    cI
    co
    wcel
    w3o
    #
    vz
    cP
    crab
    #
    cmpt2
    #
    @1
    wfn
    #
    @9
    vx
    cP
    @3
    @4
    cxp
    ciun
    #
    wfn
    #
    @10
    @11
    cvv
    @9
    wf
    #
    @12
    @8
    cvv
    wcel
    #
    vy
    @4
    wral
    vx
    cP
    wral
    @13
    @14
    vx
    vy
    cP
    @4
    @7
    vz
    cP
    cP
    cG
    cbs
    cfv
    cvv
    tglng.p
    cG
    cbs
    fvex
    eqeltri
    rabex
    rgen2w
    vx
    vy
    cP
    @4
    @8
    cvv
    @9
    @9
    eqid
    fmpt2x
    mpbi
    @11
    cvv
    @9
    ffn
    ax-mp
    @11
    @1
    @9
    vx
    cP
    cP
    xpdifid
    fneq2i
    mpbi
    @0
    @1
    cL
    @9
    vx
    vy
    vz
    cP
    cG
    cI
    cL
    tglng.p
    tglng.l
    tglng.i
    tglng
    fneq1d
    mpbiri
end
