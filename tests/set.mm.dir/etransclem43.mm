include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "dvdmsscn.mm"
include "fzfid.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cpr.mm"
include "adantr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cn.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "etransclem33.mm"
include "feqmptd.mm"
include "etransclem40.mm"
include "eqeltrrd.mm"
include "fsumcncf.mm"
include "syl5eqel.mm"

theorem etransclem43
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cM: class M
  let cX: class X
  let vk: setvar k
  assume etransclem43.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem43.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem43.p: |- ( ph -> P e. NN )
  assume etransclem43.m: |- ( ph -> M e. NN0 )
  assume etransclem43.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem43.g: |- G = ( x e. X |-> sum_ i e. ( 0 ... R ) ( ( ( S Dn F ) ` i ) ` x ) )

  disjoint F x
  disjoint M j
  disjoint M x
  disjoint j x
  disjoint P j
  disjoint P x
  disjoint R i
  disjoint R j
  disjoint R x
  disjoint i j
  disjoint i x
  disjoint S j
  disjoint S x
  disjoint X i
  disjoint X j
  disjoint X x
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> G e. ( X -cn-> CC ) )

  proof
    wph
    cG
    vx
    cX
    cc0
    cR
    cfz
    co
    #
    vx
    cv
    vi
    cv
    #
    cS
    cF
    cdvn
    co
    cfv
    #
    cfv
    #
    vi
    csu
    cmpt
    cX
    cc
    ccncf
    co
    #
    etransclem43.g
    wph
    vx
    @0
    @3
    vi
    cX
    wph
    cS
    cX
    etransclem43.s
    etransclem43.x
    dvdmsscn
    wph
    cc0
    cR
    fzfid
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @2
    vx
    cX
    @3
    cmpt
    @4
    @6
    vx
    cX
    cc
    @2
    @6
    vx
    cP
    cS
    vj
    cF
    cM
    @1
    cX
    wph
    cS
    cr
    cc
    cpr
    wcel
    @5
    etransclem43.s
    adantr
    #
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    @5
    etransclem43.x
    adantr
    #
    wph
    cP
    cn
    wcel
    @5
    etransclem43.p
    adantr
    #
    wph
    cM
    cn0
    wcel
    @5
    etransclem43.m
    adantr
    #
    etransclem43.f
    @5
    @1
    cn0
    wcel
    wph
    @1
    cR
    elfznn0
    adantl
    #
    etransclem33
    feqmptd
    @6
    vx
    cP
    cS
    vj
    cF
    cM
    @1
    cX
    @7
    @8
    @9
    @10
    etransclem43.f
    @11
    etransclem40
    eqeltrrd
    fsumcncf
    syl5eqel
end
