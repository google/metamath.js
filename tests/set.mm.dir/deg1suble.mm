include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "crg.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "deg1addle.mm"
include "wceq.mm"
include "grpsubval.mm"
include "fveq2d.mm"
include "deg1invg.mm"
include "eqcomd.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "3brtr4d.mm"

theorem deg1suble
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1suble.b: |- B = ( Base ` Y )
  assume deg1suble.m: |- .- = ( -g ` Y )
  assume deg1suble.f: |- ( ph -> F e. B )
  assume deg1suble.g: |- ( ph -> G e. B )


  assert |- ( ph -> ( D ` ( F .- G ) ) <_ if ( ( D ` F ) <_ ( D ` G ) , ( D ` G ) , ( D ` F ) ) )

  proof
    wph
    cF
    cG
    cY
    cminusg
    cfv
    #
    cfv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    cD
    cfv
    cF
    cD
    cfv
    #
    @1
    cD
    cfv
    #
    cle
    wbr
    #
    @5
    @4
    cif
    cF
    cG
    c.mi
    co
    #
    cD
    cfv
    @4
    cG
    cD
    cfv
    #
    cle
    wbr
    #
    @8
    @4
    cif
    cle
    wph
    cB
    cD
    @2
    cR
    cF
    @1
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1suble.b
    @2
    eqid
    #
    deg1suble.f
    wph
    cY
    cgrp
    wcel
    #
    cG
    cB
    wcel
    #
    @1
    cB
    wcel
    wph
    cR
    crg
    wcel
    cY
    crg
    wcel
    @11
    deg1addle.r
    cY
    cR
    deg1addle.y
    ply1ring
    cY
    ringgrp
    3syl
    deg1suble.g
    cB
    cY
    @0
    cG
    deg1suble.b
    @0
    eqid
    #
    grpinvcl
    syl2anc
    deg1addle
    wph
    @7
    @3
    cD
    wph
    cF
    cB
    wcel
    @12
    @7
    @3
    wceq
    deg1suble.f
    deg1suble.g
    cB
    @2
    cY
    @0
    c.mi
    cF
    cG
    deg1suble.b
    @10
    @13
    deg1suble.m
    grpsubval
    syl2anc
    fveq2d
    wph
    @9
    @6
    @8
    @5
    @4
    wph
    @8
    @5
    @4
    cle
    wph
    @5
    @8
    wph
    cB
    cD
    cR
    cG
    @0
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1suble.b
    @13
    deg1suble.g
    deg1invg
    eqcomd
    #
    breq2d
    @14
    ifbieq1d
    3brtr4d
end
