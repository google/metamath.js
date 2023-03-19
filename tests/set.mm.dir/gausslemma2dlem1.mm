include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "gausslemma2dlem0b.mm"
include "nnnn0d.mm"
include "fprodfac.mm"
include "syl.mm"
include "id.mm"
include "fzfid.mm"
include "cfn.mm"
include "wfn.mm"
include "crn.mm"
include "wf1o.mm"
include "fzfi.mm"
include "c2.mm"
include "cmul.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "ovex.mm"
include "ifex.mm"
include "fnmpti.mm"
include "gausslemma2dlem1a.mm"
include "rneqdmfinf1o.mm"
include "mp3an12i.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "fprodf1o.mm"
include "eqtrd.mm"

theorem gausslemma2dlem1
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cH: class H
  let vy: setvar y
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint H k
  disjoint R k
  disjoint k ph
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H l
  disjoint k l
  disjoint R l
  disjoint l ph
  assert |- ( ph -> ( ! ` H ) = prod_ k e. ( 1 ... H ) ( R ` k ) )

  proof
    wph
    cH
    cfa
    cfv
    #
    c1
    cH
    cfz
    co
    #
    vl
    cv
    #
    vl
    cprod
    #
    @1
    vk
    cv
    #
    cR
    cfv
    #
    vk
    cprod
    wph
    cH
    cn0
    wcel
    @0
    @3
    wceq
    wph
    cH
    wph
    cP
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2dlem0b
    nnnn0d
    cH
    vl
    fprodfac
    syl
    wph
    @1
    @2
    @1
    @5
    vl
    vk
    cR
    @5
    @2
    @5
    wceq
    id
    wph
    c1
    cH
    fzfid
    @1
    cfn
    wcel
    cR
    @1
    wfn
    wph
    cR
    crn
    @1
    wceq
    @1
    @1
    cR
    wf1o
    c1
    cH
    fzfi
    vx
    @1
    vx
    cv
    #
    c2
    cmul
    co
    #
    cP
    c2
    cdiv
    co
    clt
    wbr
    #
    @7
    cP
    @7
    cmin
    co
    #
    cif
    cR
    @8
    @7
    @9
    @6
    c2
    cmul
    ovex
    cP
    @7
    cmin
    ovex
    ifex
    gausslemma2d.r
    fnmpti
    wph
    vx
    cP
    cR
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2dlem1a
    @1
    cR
    rneqdmfinf1o
    mp3an12i
    wph
    @4
    @1
    wcel
    wa
    @5
    eqidd
    @2
    @1
    wcel
    #
    @2
    cc
    wcel
    wph
    @10
    @2
    @2
    c1
    cH
    elfzelz
    zcnd
    adantl
    fprodf1o
    eqtrd
end
