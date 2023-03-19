include "cco1.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "cn0.mm"
include "crg.mm"
include "wcel.mm"
include "c0g.mm"
include "wne.mm"
include "mon1pcl.mm"
include "syl.mm"
include "mon1pn0.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "cle.mm"
include "nn0red.mm"
include "leidd.mm"
include "eqbrtrd.mm"
include "cur.mm"
include "fveq2d.mm"
include "wceq.mm"
include "mon1pldg.mm"
include "eqtr3d.mm"
include "3eqtr2d.mm"
include "deg1sublt.mm"

theorem deg1submon1p
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cO: class O
  let cX: class X
  assume deg1submon1p.d: |- D = ( deg1 ` R )
  assume deg1submon1p.o: |- O = ( Monic1p ` R )
  assume deg1submon1p.p: |- P = ( Poly1 ` R )
  assume deg1submon1p.m: |- .- = ( -g ` P )
  assume deg1submon1p.r: |- ( ph -> R e. Ring )
  assume deg1submon1p.f1: |- ( ph -> F e. O )
  assume deg1submon1p.f2: |- ( ph -> ( D ` F ) = X )
  assume deg1submon1p.g1: |- ( ph -> G e. O )
  assume deg1submon1p.g2: |- ( ph -> ( D ` G ) = X )


  assert |- ( ph -> ( D ` ( F .- G ) ) < X )

  proof
    wph
    cF
    cco1
    cfv
    #
    cP
    cbs
    cfv
    #
    cG
    cco1
    cfv
    #
    cD
    cP
    cR
    cF
    cG
    cX
    c.mi
    deg1submon1p.d
    deg1submon1p.p
    @1
    eqid
    #
    deg1submon1p.m
    wph
    cF
    cD
    cfv
    #
    cX
    cn0
    deg1submon1p.f2
    wph
    cR
    crg
    wcel
    cF
    @1
    wcel
    #
    cF
    cP
    c0g
    cfv
    #
    wne
    #
    @4
    cn0
    wcel
    deg1submon1p.r
    wph
    cF
    cO
    wcel
    #
    @5
    deg1submon1p.f1
    @1
    cP
    cR
    cF
    cO
    deg1submon1p.p
    @3
    deg1submon1p.o
    mon1pcl
    syl
    #
    wph
    @8
    @7
    deg1submon1p.f1
    cP
    cR
    cF
    cO
    @6
    deg1submon1p.p
    @6
    eqid
    #
    deg1submon1p.o
    mon1pn0
    syl
    @1
    cD
    cP
    cR
    cF
    @6
    deg1submon1p.d
    deg1submon1p.p
    @10
    @3
    deg1nn0cl
    syl3anc
    eqeltrrd
    #
    deg1submon1p.r
    @9
    wph
    @4
    cX
    cX
    cle
    deg1submon1p.f2
    wph
    cX
    wph
    cX
    @11
    nn0red
    leidd
    #
    eqbrtrd
    wph
    cG
    cO
    wcel
    #
    cG
    @1
    wcel
    deg1submon1p.g1
    @1
    cP
    cR
    cG
    cO
    deg1submon1p.p
    @3
    deg1submon1p.o
    mon1pcl
    syl
    wph
    cG
    cD
    cfv
    #
    cX
    cX
    cle
    deg1submon1p.g2
    @12
    eqbrtrd
    @0
    eqid
    @2
    eqid
    wph
    cX
    @0
    cfv
    #
    cR
    cur
    cfv
    #
    @14
    @2
    cfv
    #
    cX
    @2
    cfv
    wph
    @4
    @0
    cfv
    #
    @15
    @16
    wph
    @4
    cX
    @0
    deg1submon1p.f2
    fveq2d
    wph
    @8
    @18
    @16
    wceq
    deg1submon1p.f1
    cD
    cR
    @16
    cF
    cO
    deg1submon1p.d
    @16
    eqid
    #
    deg1submon1p.o
    mon1pldg
    syl
    eqtr3d
    wph
    @13
    @17
    @16
    wceq
    deg1submon1p.g1
    cD
    cR
    @16
    cG
    cO
    deg1submon1p.d
    @19
    deg1submon1p.o
    mon1pldg
    syl
    wph
    @14
    cX
    @2
    deg1submon1p.g2
    fveq2d
    3eqtr2d
    deg1sublt
end
