include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wcel.mm"
include "cxr.mm"
include "crg.mm"
include "ply1ring.mm"
include "syl.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "deg1xrcl.mm"
include "ifcld.mm"
include "deg1addle.mm"
include "wa.mm"
include "wb.mm"
include "xrmaxle.mm"
include "mpbir2and.mm"
include "xrletrd.mm"

theorem deg1addle2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1addle.b: |- B = ( Base ` Y )
  assume deg1addle.p: |- .+ = ( +g ` Y )
  assume deg1addle.f: |- ( ph -> F e. B )
  assume deg1addle.g: |- ( ph -> G e. B )
  assume deg1addle2.l1: |- ( ph -> L e. RR* )
  assume deg1addle2.l2: |- ( ph -> ( D ` F ) <_ L )
  assume deg1addle2.l3: |- ( ph -> ( D ` G ) <_ L )


  assert |- ( ph -> ( D ` ( F .+ G ) ) <_ L )

  proof
    wph
    cF
    cG
    c.pl
    co
    #
    cD
    cfv
    #
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    cle
    wbr
    #
    @3
    @2
    cif
    #
    cL
    wph
    @0
    cB
    wcel
    #
    @1
    cxr
    wcel
    wph
    cY
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    @6
    wph
    cR
    crg
    wcel
    @7
    deg1addle.r
    cY
    cR
    deg1addle.y
    ply1ring
    syl
    deg1addle.f
    deg1addle.g
    cB
    c.pl
    cY
    cF
    cG
    deg1addle.b
    deg1addle.p
    ringacl
    syl3anc
    cB
    cD
    cY
    cR
    @0
    deg1addle.d
    deg1addle.y
    deg1addle.b
    deg1xrcl
    syl
    wph
    @4
    @3
    @2
    cxr
    wph
    @9
    @3
    cxr
    wcel
    #
    deg1addle.g
    cB
    cD
    cY
    cR
    cG
    deg1addle.d
    deg1addle.y
    deg1addle.b
    deg1xrcl
    syl
    #
    wph
    @8
    @2
    cxr
    wcel
    #
    deg1addle.f
    cB
    cD
    cY
    cR
    cF
    deg1addle.d
    deg1addle.y
    deg1addle.b
    deg1xrcl
    syl
    #
    ifcld
    deg1addle2.l1
    wph
    cB
    cD
    c.pl
    cR
    cF
    cG
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1addle.b
    deg1addle.p
    deg1addle.f
    deg1addle.g
    deg1addle
    wph
    @5
    cL
    cle
    wbr
    #
    @2
    cL
    cle
    wbr
    #
    @3
    cL
    cle
    wbr
    #
    deg1addle2.l2
    deg1addle2.l3
    wph
    @12
    @10
    cL
    cxr
    wcel
    @14
    @15
    @16
    wa
    wb
    @13
    @11
    deg1addle2.l1
    @2
    @3
    cL
    xrmaxle
    syl3anc
    mpbir2and
    xrletrd
end
