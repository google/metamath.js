include "ccop.mm"
include "cnop.mm"
include "cfv.mm"
include "cmv.mm"
include "cno.mm"
include "clo.mm"
include "wcel.mm"
include "cr.mm"
include "nmcopex.mm"
include "mpan.mm"
include "cv.mm"
include "chil.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "nmcoplb.mm"
include "mp3an1.mm"
include "wf.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "lnopfi.mm"
include "elcnop.mm"
include "mpbiran.mm"
include "ffvelrni.mm"
include "normcl.mm"
include "syl.mm"
include "lnopsubi.mm"
include "lnconi.mm"

theorem lnopconi
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vw: setvar w
  let vz: setvar z
  assume lnopcon.1: |- T e. LinOp

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T e. ContOp <-> E. x e. RR A. y e. ~H ( normh ` ( T ` y ) ) <_ ( x x. ( normh ` y ) ) )

  proof
    vx
    vy
    vz
    vw
    ccop
    cT
    cnop
    cfv
    #
    cT
    cmv
    cno
    cT
    clo
    wcel
    #
    cT
    ccop
    wcel
    #
    @0
    cr
    wcel
    lnopcon.1
    cT
    nmcopex
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
    cno
    cfv
    #
    @0
    @3
    cno
    cfv
    cmul
    co
    cle
    wbr
    lnopcon.1
    @3
    cT
    nmcoplb
    mp3an1
    @2
    chil
    chil
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
    @7
    cT
    cfv
    @8
    cT
    cfv
    cmv
    co
    cno
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
    lnopcon.1
    lnopfi
    #
    vx
    vz
    vy
    vw
    cT
    elcnop
    mpbiran
    @4
    @5
    chil
    wcel
    @6
    cr
    wcel
    chil
    chil
    @3
    cT
    @9
    ffvelrni
    @5
    normcl
    syl
    @7
    @8
    cT
    lnopcon.1
    lnopsubi
    lnconi
end
