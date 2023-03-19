include "csca.mm"
include "cfv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "ccms.mm"
include "wcel.mm"
include "cmt.mm"
include "ctps.mm"
include "cbn.mm"
include "bncms.mm"
include "syl.mm"
include "cmsms.mm"
include "mstps.mm"
include "3syl.mm"
include "clmod.mm"
include "ccmn.mm"
include "bnlmod.mm"
include "lmodcmn.mm"
include "cv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "crn.mm"
include "imassrn.mm"
include "crrh.mm"
include "rneqi.mm"
include "crrext.mm"
include "cr.mm"
include "wf.mm"
include "wss.mm"
include "rrhfe.mm"
include "frn.mm"
include "syl5eqss.mm"
include "syl5ss.mm"
include "sselda.mm"
include "3adant3.mm"
include "simp3.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "sitgclg.mm"

theorem sitgclbn
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vm: setvar m
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sibfmbl.1: |- ( ph -> F e. dom ( W sitg M ) )
  assume sitgclbn.1: |- ( ph -> W e. Ban )
  assume sitgclbn.2: |- ( ph -> ( Scalar ` W ) e. RRExt )


  assert |- ( ph -> ( ( W sitg M ) ` F ) e. B )

  proof
    wph
    vx
    cB
    cW
    csca
    cfv
    #
    cds
    cfv
    @0
    cbs
    cfv
    #
    @1
    cxp
    cres
    #
    cS
    c.x
    vm
    cF
    @0
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sibfmbl.1
    @0
    eqid
    #
    @2
    eqid
    wph
    cW
    ccms
    wcel
    #
    cW
    cmt
    wcel
    cW
    ctps
    wcel
    wph
    cW
    cbn
    wcel
    #
    @4
    sitgclbn.1
    cW
    bncms
    syl
    cW
    cmsms
    cW
    mstps
    3syl
    wph
    @5
    cW
    clmod
    wcel
    #
    cW
    ccmn
    wcel
    sitgclbn.1
    cW
    bnlmod
    #
    cW
    lmodcmn
    3syl
    sitgclbn.2
    wph
    vm
    cv
    #
    cH
    cc0
    cpnf
    cico
    co
    #
    cima
    #
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    w3a
    @6
    @8
    @1
    wcel
    #
    @13
    @8
    @12
    c.x
    co
    cB
    wcel
    wph
    @11
    @6
    @13
    wph
    @5
    @6
    sitgclbn.1
    @7
    syl
    3ad2ant1
    wph
    @11
    @14
    @13
    wph
    @10
    @1
    @8
    wph
    @10
    cH
    crn
    #
    @1
    cH
    @9
    imassrn
    wph
    @15
    @0
    crrh
    cfv
    #
    crn
    #
    @1
    cH
    @16
    sitgval.h
    rneqi
    wph
    @0
    crrext
    wcel
    cr
    @1
    @16
    wf
    @17
    @1
    wss
    sitgclbn.2
    @1
    @0
    @1
    eqid
    #
    rrhfe
    cr
    @1
    @16
    frn
    3syl
    syl5eqss
    syl5ss
    sselda
    3adant3
    wph
    @11
    @13
    simp3
    @8
    c.x
    @0
    @1
    cB
    cW
    @12
    sitgval.b
    @3
    sitgval.x
    @18
    lmodvscl
    syl3anc
    sitgclg
end
