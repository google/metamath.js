include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "cr.mm"
include "dya2iocival.mm"
include "cxr.mm"
include "wss.mm"
include "simpr.mm"
include "zred.mm"
include "crp.mm"
include "2rp.mm"
include "a1i.mm"
include "simpl.mm"
include "rpexpcld.mm"
include "rerpdivcld.mm"
include "1red.mm"
include "readdcld.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "eqsstrd.mm"

theorem dya2iocress
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )

  disjoint n x
  assert |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) C_ RR )

  proof
    cN
    cz
    wcel
    #
    cX
    cz
    wcel
    #
    wa
    #
    cX
    cN
    cI
    co
    cX
    c2
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cX
    c1
    caddc
    co
    #
    @3
    cdiv
    co
    #
    cico
    co
    #
    cr
    vx
    vn
    cI
    cJ
    cN
    cX
    sxbrsiga.0
    dya2ioc.1
    dya2iocival
    @2
    @4
    cr
    wcel
    @6
    cxr
    wcel
    @7
    cr
    wss
    @2
    cX
    @3
    @2
    cX
    @0
    @1
    simpr
    zred
    #
    @2
    c2
    cN
    c2
    crp
    wcel
    @2
    2rp
    a1i
    @0
    @1
    simpl
    rpexpcld
    #
    rerpdivcld
    @2
    @6
    @2
    @5
    @3
    @2
    cX
    c1
    @8
    @2
    1red
    readdcld
    @9
    rerpdivcld
    rexrd
    @4
    @6
    icossre
    syl2anc
    eqsstrd
end
