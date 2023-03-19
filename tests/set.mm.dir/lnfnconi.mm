include "ccnfn.mm"
include "cnmf.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "clf.mm"
include "wcel.mm"
include "cr.mm"
include "nmcfnex.mm"
include "mpan.mm"
include "cv.mm"
include "chil.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "nmcfnlb.mm"
include "mp3an1.mm"
include "cc.mm"
include "wf.mm"
include "cmv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "lnfnfi.mm"
include "elcnfn.mm"
include "mpbiran.mm"
include "ffvelrni.mm"
include "abscld.mm"
include "lnfnsubi.mm"
include "lnconi.mm"

theorem lnfnconi
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vz: setvar z
  let vw: setvar w
  assume lnfncon.1: |- T e. LinFn

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint T z
  disjoint T w
  assert |- ( T e. ContFn <-> E. x e. RR A. y e. ~H ( abs ` ( T ` y ) ) <_ ( x x. ( normh ` y ) ) )

  proof
    vx
    vy
    vz
    vw
    ccnfn
    cT
    cnmf
    cfv
    #
    cT
    cmin
    cabs
    cT
    clf
    wcel
    #
    cT
    ccnfn
    wcel
    #
    @0
    cr
    wcel
    lnfncon.1
    cT
    nmcfnex
    mpan
    @1
    @2
    vy
    cv
    #
    chil
    wcel
    #
    @3
    cT
    cfv
    #
    cabs
    cfv
    @0
    @3
    cno
    cfv
    cmul
    co
    cle
    wbr
    lnfncon.1
    @3
    cT
    nmcfnlb
    mp3an1
    @2
    chil
    cc
    cT
    wf
    vw
    cv
    #
    vx
    cv
    #
    cmv
    co
    cno
    cfv
    @3
    clt
    wbr
    @6
    cT
    cfv
    @7
    cT
    cfv
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    wi
    vw
    chil
    wral
    vy
    crp
    wrex
    vz
    crp
    wral
    vx
    chil
    wral
    cT
    lnfncon.1
    lnfnfi
    #
    vx
    vz
    vy
    vw
    cT
    elcnfn
    mpbiran
    @4
    @5
    chil
    cc
    @3
    cT
    @8
    ffvelrni
    abscld
    @6
    @7
    cT
    lnfncon.1
    lnfnsubi
    lnconi
end
