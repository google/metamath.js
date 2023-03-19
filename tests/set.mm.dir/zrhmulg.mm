include "crg.mm"
include "wcel.mm"
include "cz.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "zrhval2.mm"
include "fveq1d.mm"
include "oveq1.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem zrhmulg
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cL: class L
  let cN: class N
  let vr: setvar r
  let vs: setvar s
  let vn: setvar n
  assume zrhval.l: |- L = ( ZRHom ` R )
  assume zrhval2.m: |- .x. = ( .g ` R )
  assume zrhval2.1: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ N e. ZZ ) -> ( L ` N ) = ( N .x. .1. ) )

  proof
    cR
    crg
    wcel
    #
    cN
    cz
    wcel
    cN
    cL
    cfv
    cN
    vn
    cz
    vn
    cv
    #
    c.1
    c.x
    co
    #
    cmpt
    #
    cfv
    cN
    c.1
    c.x
    co
    #
    @0
    cN
    cL
    @3
    cR
    c.x
    c.1
    vn
    cL
    zrhval.l
    zrhval2.m
    zrhval2.1
    zrhval2
    fveq1d
    vn
    cN
    @2
    @4
    cz
    @3
    @1
    cN
    c.1
    c.x
    oveq1
    @3
    eqid
    cN
    c.1
    c.x
    ovex
    fvmpt
    sylan9eq
end
