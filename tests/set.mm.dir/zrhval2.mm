include "crg.mm"
include "wcel.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "cuni.mm"
include "cz.mm"
include "cv.mm"
include "cmpt.mm"
include "zrhval.mm"
include "csn.mm"
include "eqid.mm"
include "mulgrhm2.mm"
include "unieqd.mm"
include "zex.mm"
include "mptex.mm"
include "unisn.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem zrhval2
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vn: setvar n
  let cL: class L
  let vr: setvar r
  let vs: setvar s
  let cN: class N
  assume zrhval.l: |- L = ( ZRHom ` R )
  assume zrhval2.m: |- .x. = ( .g ` R )
  assume zrhval2.1: |- .1. = ( 1r ` R )

  disjoint .1. n
  disjoint R n
  disjoint .x. n
  disjoint r s
  disjoint N n
  disjoint n r
  disjoint R r
  assert |- ( R e. Ring -> L = ( n e. ZZ |-> ( n .x. .1. ) ) )

  proof
    cR
    crg
    wcel
    #
    cL
    zring
    cR
    crh
    co
    #
    cuni
    #
    vn
    cz
    vn
    cv
    c.1
    c.x
    co
    #
    cmpt
    #
    cR
    cL
    zrhval.l
    zrhval
    @0
    @2
    @4
    csn
    #
    cuni
    @4
    @0
    @1
    @5
    cR
    c.x
    c.1
    vn
    @4
    zrhval2.m
    @4
    eqid
    zrhval2.1
    mulgrhm2
    unieqd
    @4
    vn
    cz
    @3
    zex
    mptex
    unisn
    syl6eq
    syl5eq
end
