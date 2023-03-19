include "wcel.mm"
include "cec.mm"
include "cqs.mm"
include "cefg.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ecelqsi.mm"
include "cbs.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cqus.mm"
include "co.mm"
include "wceq.mm"
include "cword.mm"
include "efgrcl.mm"
include "simpld.mm"
include "eqid.mm"
include "frgpval.mm"
include "syl.mm"
include "simprd.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "a1i.mm"
include "fvexd.mm"
include "qusbas.mm"
include "syl6eqr.mm"
include "eleqtrd.mm"

theorem frgpeccl
  let cB: class B
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  let cV: class V
  assume frgp0.m: |- G = ( freeGrp ` I )
  assume frgp0.r: |- .~ = ( ~FG ` I )
  assume frgpeccl.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpeccl.b: |- B = ( Base ` G )


  assert |- ( X e. W -> [ X ] .~ e. B )

  proof
    cX
    cW
    wcel
    #
    cX
    c.sm
    cec
    cW
    c.sm
    cqs
    #
    cB
    cW
    cX
    c.sm
    c.sm
    cI
    cefg
    cfv
    cvv
    frgp0.r
    cI
    cefg
    fvex
    eqeltri
    #
    ecelqsi
    @0
    @1
    cG
    cbs
    cfv
    cB
    @0
    c.sm
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    cG
    cW
    cvv
    cvv
    @0
    cI
    cvv
    wcel
    #
    cG
    @4
    c.sm
    cqus
    co
    wceq
    @0
    @5
    cW
    @3
    cword
    #
    wceq
    #
    cX
    cI
    cW
    frgpeccl.w
    efgrcl
    #
    simpld
    #
    c.sm
    cG
    cI
    @4
    cvv
    frgp0.m
    @4
    eqid
    #
    frgp0.r
    frgpval
    syl
    @0
    cW
    @6
    @4
    cbs
    cfv
    #
    @0
    @5
    @7
    @8
    simprd
    @0
    @3
    cvv
    wcel
    #
    @11
    @6
    wceq
    @0
    @5
    c2o
    con0
    wcel
    @12
    @9
    2on
    cI
    c2o
    cvv
    con0
    xpexg
    sylancl
    @11
    @3
    @4
    cvv
    @10
    @11
    eqid
    frmdbas
    syl
    eqtr4d
    c.sm
    cvv
    wcel
    @0
    @2
    a1i
    @0
    @3
    cfrmd
    fvexd
    qusbas
    frgpeccl.b
    syl6eqr
    eleqtrd
end
