include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "co.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cfv.mm"
include "cplusg.mm"
include "cconcat.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "cmnd.mm"
include "cvv.mm"
include "cqus.mm"
include "cword.mm"
include "efgrcl.mm"
include "adantr.mm"
include "simpld.mm"
include "eqid.mm"
include "frgpval.mm"
include "syl.mm"
include "cbs.mm"
include "simprd.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "frmdmnd.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "frgpcpbl.mm"
include "simprl.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "qusaddval.mm"
include "mpd3an23.mm"
include "frmdadd.mm"
include "syl2anc.mm"
include "eceq1d.mm"
include "eqtrd.mm"

theorem frgpadd
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume frgpadd.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpadd.g: |- G = ( freeGrp ` I )
  assume frgpadd.r: |- .~ = ( ~FG ` I )
  assume frgpadd.n: |- .+ = ( +g ` G )


  assert |- ( ( A e. W /\ B e. W ) -> ( [ A ] .~ .+ [ B ] .~ ) = [ ( A ++ B ) ] .~ )

  proof
    cA
    cW
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    c.sm
    cec
    cB
    c.sm
    cec
    c.pl
    co
    #
    cA
    cB
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    c.sm
    cec
    #
    cA
    cB
    cconcat
    co
    #
    c.sm
    cec
    @2
    @0
    @1
    @3
    @8
    wceq
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    c.sm
    @5
    c.pl
    @6
    cG
    cW
    cA
    cB
    cmnd
    vd
    vb
    va
    vc
    @2
    cI
    cvv
    wcel
    #
    cG
    @5
    c.sm
    cqus
    co
    wceq
    @2
    @12
    cW
    @4
    cword
    #
    wceq
    #
    @0
    @12
    @14
    wa
    @1
    cA
    cI
    cW
    frgpadd.w
    efgrcl
    adantr
    #
    simpld
    #
    c.sm
    cG
    cI
    @5
    cvv
    frgpadd.g
    @5
    eqid
    #
    frgpadd.r
    frgpval
    syl
    @2
    cW
    @13
    @5
    cbs
    cfv
    #
    @2
    @12
    @14
    @15
    simprd
    @2
    @4
    cvv
    wcel
    #
    @18
    @13
    wceq
    @2
    @12
    c2o
    con0
    wcel
    @19
    @16
    2on
    cI
    c2o
    cvv
    con0
    xpexg
    sylancl
    #
    @18
    @4
    @5
    cvv
    @17
    @18
    eqid
    #
    frmdbas
    syl
    eqtr4d
    #
    cW
    c.sm
    wer
    @2
    c.sm
    cI
    cW
    frgpadd.w
    frgpadd.r
    efger
    a1i
    @2
    @19
    @5
    cmnd
    wcel
    #
    @20
    @4
    @5
    cvv
    @17
    frmdmnd
    syl
    #
    va
    cv
    #
    vb
    cv
    #
    c.sm
    wbr
    vc
    cv
    #
    vd
    cv
    #
    c.sm
    wbr
    wa
    @25
    @27
    @6
    co
    @26
    @28
    @6
    co
    #
    c.sm
    wbr
    wi
    @2
    @25
    @27
    @26
    @28
    @6
    c.sm
    cG
    cI
    @5
    frgpadd.g
    @17
    frgpadd.r
    @6
    eqid
    #
    frgpcpbl
    a1i
    @2
    @26
    cW
    wcel
    #
    @28
    cW
    wcel
    #
    wa
    #
    wa
    #
    @29
    @18
    cW
    @34
    @23
    @26
    @18
    wcel
    @28
    @18
    wcel
    @29
    @18
    wcel
    @2
    @23
    @33
    @24
    adantr
    @34
    @26
    cW
    @18
    @2
    @31
    @32
    simprl
    @2
    cW
    @18
    wceq
    @33
    @22
    adantr
    #
    eleqtrd
    @34
    @28
    cW
    @18
    @2
    @31
    @32
    simprr
    @35
    eleqtrd
    @18
    @6
    @5
    @26
    @28
    @21
    @30
    mndcl
    syl3anc
    @35
    eleqtrrd
    @30
    frgpadd.n
    qusaddval
    mpd3an23
    @2
    @7
    @9
    c.sm
    @2
    cA
    @18
    wcel
    cB
    @18
    wcel
    @7
    @9
    wceq
    @2
    cA
    cW
    @18
    @10
    @22
    eleqtrd
    @2
    cB
    cW
    @18
    @11
    @22
    eleqtrd
    @18
    @6
    @4
    @5
    cA
    cB
    @17
    @21
    @30
    frmdadd
    syl2anc
    eceq1d
    eqtrd
end
