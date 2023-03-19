include "csm.mm"
include "cva.mm"
include "cno.mm"
include "chil.mm"
include "c0v.mm"
include "cablo.mm"
include "wcel.mm"
include "cgr.mm"
include "hilablo.mm"
include "ablogrpo.mm"
include "ax-mp.mm"
include "cxp.mm"
include "ax-hfvadd.mm"
include "fdmi.mm"
include "grporn.mm"
include "cgi.mm"
include "cfv.mm"
include "hilid.mm"
include "eqcomi.mm"
include "hilvc.mm"
include "normf.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "norm-i.mm"
include "biimpa.mm"
include "norm-iii.mm"
include "norm-ii.mm"
include "isnvi.mm"

theorem hhnv
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  assume hhnv.1: |- U = <. <. +h , .h >. , normh >.


  assert |- U e. NrmCVec

  proof
    vx
    vy
    csm
    cU
    cva
    cno
    chil
    c0v
    cva
    chil
    cva
    cablo
    wcel
    cva
    cgr
    wcel
    hilablo
    cva
    ablogrpo
    ax-mp
    chil
    chil
    cxp
    chil
    cva
    ax-hfvadd
    fdmi
    grporn
    cva
    cgi
    cfv
    c0v
    hilid
    eqcomi
    hilvc
    normf
    vx
    cv
    #
    chil
    wcel
    @0
    cno
    cfv
    cc0
    wceq
    @0
    c0v
    wceq
    @0
    norm-i
    biimpa
    vy
    cv
    #
    @0
    norm-iii
    @0
    @1
    norm-ii
    hhnv.1
    isnvi
end
