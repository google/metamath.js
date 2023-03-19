include "cnop.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "chos.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "bdophsi.mm"
include "cc.mm"
include "wcel.mm"
include "cbo.mm"
include "neg1cn.mm"
include "bdophmi.mm"
include "ax-mp.mm"
include "nmoptrii.mm"
include "chod.mm"
include "chil.mm"
include "wf.mm"
include "bdopf.mm"
include "hoaddcli.mm"
include "honegsubi.mm"
include "hopncani.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "nmopnegi.mm"
include "oveq2i.mm"
include "3brtr3i.mm"
include "cr.mm"
include "nmopre.mm"
include "lesubaddi.mm"
include "mpbir.mm"

theorem nmoptri2i
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  assume nmoptri.1: |- S e. BndLinOp
  assume nmoptri.2: |- T e. BndLinOp


  assert |- ( ( normop ` S ) - ( normop ` T ) ) <_ ( normop ` ( S +op T ) )

  proof
    cS
    cnop
    cfv
    #
    cT
    cnop
    cfv
    #
    cmin
    co
    cS
    cT
    chos
    co
    #
    cnop
    cfv
    #
    cle
    wbr
    @0
    @3
    @1
    caddc
    co
    #
    cle
    wbr
    @2
    c1
    cneg
    #
    cT
    chot
    co
    #
    chos
    co
    #
    cnop
    cfv
    @3
    @6
    cnop
    cfv
    #
    caddc
    co
    @0
    @4
    cle
    @2
    @6
    cS
    cT
    nmoptri.1
    nmoptri.2
    bdophsi
    #
    @5
    cc
    wcel
    @6
    cbo
    wcel
    neg1cn
    @5
    cT
    nmoptri.2
    bdophmi
    ax-mp
    nmoptrii
    @7
    cS
    cnop
    @7
    @2
    cT
    chod
    co
    cS
    @2
    cT
    cS
    cT
    cS
    cbo
    wcel
    #
    chil
    chil
    cS
    wf
    nmoptri.1
    cS
    bdopf
    ax-mp
    #
    cT
    cbo
    wcel
    #
    chil
    chil
    cT
    wf
    nmoptri.2
    cT
    bdopf
    ax-mp
    #
    hoaddcli
    @13
    honegsubi
    cS
    cT
    @11
    @13
    hopncani
    eqtri
    fveq2i
    @8
    @1
    @3
    caddc
    cT
    @13
    nmopnegi
    oveq2i
    3brtr3i
    @0
    @1
    @3
    @10
    @0
    cr
    wcel
    nmoptri.1
    cS
    nmopre
    ax-mp
    @12
    @1
    cr
    wcel
    nmoptri.2
    cT
    nmopre
    ax-mp
    @2
    cbo
    wcel
    @3
    cr
    wcel
    @9
    @2
    nmopre
    ax-mp
    lesubaddi
    mpbir
end
