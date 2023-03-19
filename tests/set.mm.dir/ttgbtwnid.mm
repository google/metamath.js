include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "simpll.mm"
include "simpr.mm"
include "clmod.mm"
include "cclm.mm"
include "clmlmod.mm"
include "syl.mm"
include "eqid.mm"
include "lmodsubid.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "oveq2d.mm"
include "wss.mm"
include "simplr.mm"
include "sseldd.mm"
include "csca.mm"
include "lmodvs0.mm"
include "3eqtrd.mm"
include "wb.mm"
include "lmodsubeq0.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "eqcomd.mm"
include "wrex.mm"
include "ttgelitv.mm"
include "mpbid.mm"
include "r19.29a.mm"

theorem ttgbtwnid
  let wph: wff ph
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cZ: class Z
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgitvval.i: |- I = ( Itv ` G )
  assume ttgitvval.b: |- P = ( Base ` H )
  assume ttgitvval.m: |- .- = ( -g ` H )
  assume ttgitvval.s: |- .x. = ( .s ` H )
  assume ttgelitv.x: |- ( ph -> X e. P )
  assume ttgelitv.y: |- ( ph -> Y e. P )
  assume ttgbtwnid.r: |- R = ( Base ` ( Scalar ` H ) )
  assume ttgbtwnid.2: |- ( ph -> ( 0 [,] 1 ) C_ R )
  assume ttgbtwnid.1: |- ( ph -> H e. CMod )
  assume ttgbtwnid.y: |- ( ph -> Y e. ( X I X ) )


  assert |- ( ph -> X = Y )

  proof
    wph
    cY
    cX
    c.mi
    co
    #
    vk
    cv
    #
    cX
    cX
    c.mi
    co
    #
    c.x
    co
    #
    wceq
    #
    cX
    cY
    wceq
    vk
    cc0
    c1
    cicc
    co
    #
    wph
    @1
    @5
    wcel
    #
    wa
    #
    @4
    wa
    #
    cY
    cX
    @8
    wph
    @0
    cH
    c0g
    cfv
    #
    wceq
    #
    cY
    cX
    wceq
    #
    wph
    @6
    @4
    simpll
    @8
    @0
    @3
    @1
    @9
    c.x
    co
    #
    @9
    @7
    @4
    simpr
    @8
    @2
    @9
    @1
    c.x
    wph
    @2
    @9
    wceq
    #
    @6
    @4
    wph
    cH
    clmod
    wcel
    #
    cX
    cP
    wcel
    #
    @13
    wph
    cH
    cclm
    wcel
    @14
    ttgbtwnid.1
    cH
    clmlmod
    syl
    #
    ttgelitv.x
    cX
    c.mi
    cP
    cH
    @9
    ttgitvval.b
    @9
    eqid
    #
    ttgitvval.m
    lmodsubid
    syl2anc
    ad2antrr
    oveq2d
    @8
    @14
    @1
    cR
    wcel
    @12
    @9
    wceq
    wph
    @14
    @6
    @4
    @16
    ad2antrr
    @8
    @5
    cR
    @1
    wph
    @5
    cR
    wss
    @6
    @4
    ttgbtwnid.2
    ad2antrr
    wph
    @6
    @4
    simplr
    sseldd
    c.x
    cH
    csca
    cfv
    #
    cR
    cH
    @1
    @9
    @18
    eqid
    ttgitvval.s
    ttgbtwnid.r
    @17
    lmodvs0
    syl2anc
    3eqtrd
    wph
    @10
    @11
    wph
    @14
    cY
    cP
    wcel
    @15
    @10
    @11
    wb
    @16
    ttgelitv.y
    ttgelitv.x
    cY
    cX
    c.mi
    cP
    cH
    @9
    ttgitvval.b
    @17
    ttgitvval.m
    lmodsubeq0
    syl3anc
    biimpa
    syl2anc
    eqcomd
    wph
    cY
    cX
    cX
    cI
    co
    wcel
    @4
    vk
    @5
    wrex
    ttgbtwnid.y
    wph
    cP
    c.x
    vk
    cG
    cH
    cI
    c.mi
    cclm
    cX
    cX
    cY
    ttgval.n
    ttgitvval.i
    ttgitvval.b
    ttgitvval.m
    ttgitvval.s
    ttgelitv.x
    ttgelitv.x
    ttgbtwnid.1
    ttgelitv.y
    ttgelitv
    mpbid
    r19.29a
end
