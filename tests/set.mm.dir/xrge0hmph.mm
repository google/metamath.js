include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cpnf.mm"
include "cmin.mm"
include "cdiv.mm"
include "cif.mm"
include "cmpt.mm"
include "cii.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "chmeo.mm"
include "wcel.mm"
include "chmph.mm"
include "wbr.mm"
include "clt.mm"
include "wiso.mm"
include "eqid.mm"
include "iccpnfhmeo.mm"
include "simpri.mm"
include "hmphi.mm"
include "ax-mp.mm"

theorem xrge0hmph
  let vx: setvar x


  assert |- II ~= ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )

  proof
    vx
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    c1
    wceq
    cpnf
    @1
    c1
    @1
    cmin
    co
    cdiv
    co
    cif
    cmpt
    #
    cii
    cle
    cordt
    cfv
    cc0
    cpnf
    cicc
    co
    #
    crest
    co
    #
    chmeo
    co
    wcel
    #
    cii
    @4
    chmph
    wbr
    @0
    @3
    clt
    clt
    @2
    wiso
    @5
    vx
    @2
    @4
    @2
    eqid
    @4
    eqid
    iccpnfhmeo
    simpri
    @2
    cii
    @4
    hmphi
    ax-mp
end
