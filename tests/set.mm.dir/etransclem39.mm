include "cr.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "csu.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "fzfid.mm"
include "wf.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "a1i.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "reopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "cn.mm"
include "adantr.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "etransclem33.mm"
include "adantlr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "fsumcl.mm"
include "fmptd.mm"

theorem etransclem39
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cM: class M
  let vk: setvar k
  assume etransclem39.p: |- ( ph -> P e. NN )
  assume etransclem39.m: |- ( ph -> M e. NN0 )
  assume etransclem39.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem39.g: |- G = ( x e. RR |-> sum_ i e. ( 0 ... R ) ( ( ( RR Dn F ) ` i ) ` x ) )

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
  disjoint i ph
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> G : RR --> CC )

  proof
    wph
    vx
    cr
    cc0
    cR
    cfz
    co
    #
    vx
    cv
    #
    vi
    cv
    #
    cr
    cF
    cdvn
    co
    cfv
    #
    cfv
    #
    vi
    csu
    cc
    cG
    wph
    @1
    cr
    wcel
    #
    wa
    #
    @0
    @4
    vi
    @6
    cc0
    cR
    fzfid
    @6
    @2
    @0
    wcel
    #
    wa
    cr
    cc
    @1
    @3
    wph
    @7
    cr
    cc
    @3
    wf
    @5
    wph
    @7
    wa
    #
    vx
    cP
    cr
    vj
    cF
    cM
    @2
    cr
    cr
    cr
    cc
    cpr
    wcel
    @8
    reelprrecn
    a1i
    cr
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    @8
    cr
    cioo
    crn
    ctg
    cfv
    @10
    reopn
    @9
    @9
    eqid
    tgioo2
    eleqtri
    a1i
    wph
    cP
    cn
    wcel
    @7
    etransclem39.p
    adantr
    wph
    cM
    cn0
    wcel
    @7
    etransclem39.m
    adantr
    etransclem39.f
    @7
    @2
    cn0
    wcel
    wph
    @2
    cR
    elfznn0
    adantl
    etransclem33
    adantlr
    wph
    @5
    @7
    simplr
    ffvelrnd
    fsumcl
    etransclem39.g
    fmptd
end
