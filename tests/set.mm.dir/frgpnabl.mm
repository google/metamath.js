include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wn.mm"
include "wrex.mm"
include "cabl.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "1sdom.mm"
include "syl.mm"
include "ibi.mm"
include "wa.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cdif.mm"
include "cop.mm"
include "cmpt2.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cplusg.mm"
include "cefg.mm"
include "cvrgp.mm"
include "eqid.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simplrr.mm"
include "cbs.mm"
include "simpr.mm"
include "wf.mm"
include "vrgpf.mm"
include "ffvelrnd.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "frgpnabllem2.mm"
include "ex.mm"
include "con3d.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem frgpnabl
  let cG: class G
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vx: setvar x
  let cA: class A
  let vm: setvar m
  let vt: setvar t
  let cD: class D
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let c.sm: class .~
  let cB: class B
  let vk: setvar k
  let cW: class W
  let cM: class M
  let cT: class T
  assume frgpnabl.g: |- G = ( freeGrp ` I )


  assert |- ( 1o ~< I -> -. G e. Abel )

  proof
    c1o
    cI
    csdm
    wbr
    #
    va
    cv
    #
    vb
    cv
    #
    wceq
    #
    wn
    #
    vb
    cI
    wrex
    va
    cI
    wrex
    #
    cG
    cabl
    wcel
    #
    wn
    #
    @0
    @5
    @0
    cI
    cvv
    wcel
    #
    @0
    @5
    wb
    c1o
    cI
    csdm
    relsdom
    brrelex2i
    #
    va
    vb
    cI
    cvv
    1sdom
    syl
    ibi
    @0
    @4
    @7
    va
    vb
    cI
    cI
    @0
    @1
    cI
    wcel
    #
    @2
    cI
    wcel
    #
    wa
    #
    wa
    #
    @6
    @3
    @13
    @6
    @3
    @13
    @6
    wa
    #
    vx
    vy
    vz
    vw
    vv
    @1
    @2
    cI
    c2o
    cxp
    #
    cword
    cid
    cfv
    #
    vx
    @16
    vx
    cv
    vv
    @16
    vn
    vw
    cc0
    vv
    cv
    #
    chash
    cfv
    cfz
    co
    @15
    @17
    vn
    cv
    #
    @18
    vw
    cv
    #
    @19
    vy
    vz
    cI
    c2o
    vy
    cv
    c1o
    vz
    cv
    cdif
    cop
    cmpt2
    #
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    cmpt
    #
    cfv
    crn
    ciun
    cdif
    #
    cG
    cplusg
    cfv
    #
    cI
    cefg
    cfv
    #
    @21
    cI
    cvrgp
    cfv
    #
    vn
    cG
    cI
    @20
    @16
    frgpnabl.g
    @16
    eqid
    @24
    eqid
    #
    @23
    eqid
    #
    @20
    eqid
    @21
    eqid
    @22
    eqid
    @25
    eqid
    #
    @0
    @8
    @12
    @6
    @9
    ad2antrr
    #
    @0
    @10
    @11
    @6
    simplrl
    #
    @0
    @10
    @11
    @6
    simplrr
    #
    @14
    @6
    @1
    @25
    cfv
    #
    cG
    cbs
    cfv
    #
    wcel
    @2
    @25
    cfv
    #
    @33
    wcel
    @32
    @34
    @23
    co
    @34
    @32
    @23
    co
    wceq
    @13
    @6
    simpr
    @14
    cI
    @33
    @1
    @25
    @14
    @8
    cI
    @33
    @25
    wf
    @29
    @24
    @25
    cG
    cI
    cvv
    @33
    @26
    @28
    frgpnabl.g
    @33
    eqid
    #
    vrgpf
    syl
    #
    @30
    ffvelrnd
    @14
    cI
    @33
    @2
    @25
    @36
    @31
    ffvelrnd
    @33
    @23
    cG
    @32
    @34
    @35
    @27
    ablcom
    syl3anc
    frgpnabllem2
    ex
    con3d
    rexlimdvva
    mpd
end
