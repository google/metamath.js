include "cgsu.mm"
include "co.mm"
include "cdprd.mm"
include "wcel.mm"
include "cdm.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wa.mm"
include "wb.mm"
include "eldprd.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem eldprdi
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let c.mi: class .-
  let vk: setvar k
  let vx: setvar x
  let c.pl: class .+
  let vn: setvar n
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let cH: class H
  let cN: class N
  let cX: class X
  assume eldprdi.0: |- .0. = ( 0g ` G )
  assume eldprdi.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume eldprdi.1: |- ( ph -> G dom DProd S )
  assume eldprdi.2: |- ( ph -> dom S = I )
  assume eldprdi.3: |- ( ph -> F e. W )

  disjoint F h
  disjoint h i
  disjoint G h
  disjoint G i
  disjoint I h
  disjoint I i
  disjoint .0. h
  disjoint S h
  disjoint S i
  disjoint .- k
  disjoint h k
  disjoint h x
  disjoint .+ h
  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint h n
  disjoint A h
  disjoint A n
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint h y
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint H h
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint f i
  disjoint f n
  disjoint G f
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint k n
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint I f
  disjoint I k
  disjoint I n
  disjoint I x
  disjoint I y
  disjoint N h
  disjoint N x
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint .0. k
  disjoint .0. n
  disjoint .0. x
  disjoint .0. y
  disjoint S f
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint W f
  disjoint X h
  disjoint X n
  assert |- ( ph -> ( G gsum F ) e. ( G DProd S ) )

  proof
    wph
    cG
    cF
    cgsu
    co
    #
    cG
    cS
    cdprd
    co
    wcel
    #
    cG
    cS
    cdprd
    cdm
    wbr
    #
    @0
    cG
    vf
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cW
    wrex
    #
    eldprdi.1
    wph
    cF
    cW
    wcel
    @0
    @0
    wceq
    #
    @6
    eldprdi.3
    @0
    eqid
    @5
    @7
    vf
    cF
    cW
    @3
    cF
    wceq
    @4
    @0
    @0
    @3
    cF
    cG
    cgsu
    oveq2
    eqeq2d
    rspcev
    sylancl
    wph
    cS
    cdm
    cI
    wceq
    @1
    @2
    @6
    wa
    wb
    eldprdi.2
    @0
    cS
    vf
    vh
    vi
    cG
    cI
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprd
    syl
    mpbir2and
end
