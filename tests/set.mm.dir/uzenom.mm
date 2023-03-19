include "cz.mm"
include "wcel.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "breq1d.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "wf1o.mm"
include "omex.mm"
include "fvex.mm"
include "0z.mm"
include "elimel.mm"
include "eqid.mm"
include "om2uzf1oi.mm"
include "f1oen2g.mm"
include "mp3an.mm"
include "ensymi.mm"
include "dedth.mm"

theorem uzenom
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume uzinf.1: |- Z = ( ZZ>= ` M )


  assert |- ( M e. ZZ -> Z ~~ _om )

  proof
    cM
    cz
    wcel
    #
    cZ
    com
    cen
    wbr
    @0
    cM
    cc0
    cif
    #
    cuz
    cfv
    #
    com
    cen
    wbr
    cM
    cc0
    cM
    @1
    wceq
    #
    cZ
    @2
    com
    cen
    @3
    cZ
    cM
    cuz
    cfv
    @2
    uzinf.1
    cM
    @1
    cuz
    fveq2
    syl5eq
    breq1d
    com
    @2
    com
    cvv
    wcel
    @2
    cvv
    wcel
    com
    @2
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    @1
    crdg
    com
    cres
    #
    wf1o
    com
    @2
    cen
    wbr
    omex
    @1
    cuz
    fvex
    vx
    @1
    @4
    cM
    cc0
    cz
    0z
    elimel
    @4
    eqid
    om2uzf1oi
    com
    @2
    @4
    cvv
    cvv
    f1oen2g
    mp3an
    ensymi
    dedth
end
