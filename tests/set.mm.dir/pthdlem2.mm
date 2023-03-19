include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cpr.mm"
include "cima.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wn.mm"
include "cn.mm"
include "wcel.mm"
include "cvv.mm"
include "cword.mm"
include "cn0.mm"
include "wi.mm"
include "lencl.mm"
include "wne.mm"
include "df-ne.mm"
include "elnnne0.mm"
include "simplbi2.mm"
include "syl5bir.mm"
include "3syl.mm"
include "wa.mm"
include "wnel.mm"
include "wo.mm"
include "eqid.mm"
include "orci.mm"
include "pthdlem2lem.mm"
include "mp3an3.mm"
include "olci.mm"
include "cfz.mm"
include "wf.mm"
include "wb.mm"
include "cmin.mm"
include "wrdffz.mm"
include "syl.mm"
include "adantr.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "sylibr.mm"
include "nnm1nn0.mm"
include "syl5eqel.mm"
include "adantl.mm"
include "fvinim0ffz.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ex.mm"
include "syld.mm"
include "oveq1.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "c2.mm"
include "0le2.mm"
include "1p1e2.mm"
include "breqtrri.mm"
include "0re.mm"
include "1re.mm"
include "lesubadd2i.mm"
include "mpbir.mm"
include "cz.mm"
include "1z.mm"
include "0z.mm"
include "peano2zm.mm"
include "ax-mp.mm"
include "fzon.mm"
include "mp2an.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "ineq2d.mm"
include "in0.mm"
include "pm2.61d2.mm"

theorem pthdlem2
  let wph: wff ph
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  assume pthd.p: |- ( ph -> P e. Word _V )
  assume pthd.r: |- R = ( ( # ` P ) - 1 )
  assume pthd.s: |- ( ph -> A. i e. ( 0 ..^ ( # ` P ) ) A. j e. ( 1 ..^ R ) ( i =/= j -> ( P ` i ) =/= ( P ` j ) ) )

  disjoint P i
  disjoint P j
  disjoint i j
  disjoint R i
  disjoint R j
  disjoint i ph
  disjoint j ph
  disjoint I i
  disjoint I j
  assert |- ( ph -> ( ( P " { 0 , R } ) i^i ( P " ( 1 ..^ R ) ) ) = (/) )

  proof
    wph
    cP
    chash
    cfv
    #
    cc0
    wceq
    #
    cP
    cc0
    cR
    cpr
    cima
    #
    cP
    c1
    cR
    cfzo
    co
    #
    cima
    #
    cin
    #
    c0
    wceq
    #
    wph
    @1
    wn
    #
    @0
    cn
    wcel
    #
    @6
    wph
    cP
    cvv
    cword
    wcel
    #
    @0
    cn0
    wcel
    #
    @7
    @8
    wi
    pthd.p
    cvv
    cP
    lencl
    @7
    @0
    cc0
    wne
    #
    @10
    @8
    @0
    cc0
    df-ne
    @8
    @10
    @11
    @0
    elnnne0
    simplbi2
    syl5bir
    3syl
    wph
    @8
    @6
    wph
    @8
    wa
    #
    @6
    cc0
    cP
    cfv
    @4
    wnel
    #
    cR
    cP
    cfv
    @4
    wnel
    #
    wph
    @8
    cc0
    cc0
    wceq
    #
    cc0
    cR
    wceq
    #
    wo
    @13
    @15
    @16
    cc0
    eqid
    orci
    wph
    cP
    cR
    vi
    vj
    cc0
    pthd.p
    pthd.r
    pthd.s
    pthdlem2lem
    mp3an3
    wph
    @8
    cR
    cc0
    wceq
    #
    cR
    cR
    wceq
    #
    wo
    @14
    @18
    @17
    cR
    eqid
    olci
    wph
    cP
    cR
    vi
    vj
    cR
    pthd.p
    pthd.r
    pthd.s
    pthdlem2lem
    mp3an3
    @12
    cc0
    cR
    cfz
    co
    #
    cvv
    cP
    wf
    #
    cR
    cn0
    wcel
    #
    @6
    @13
    @14
    wa
    wb
    @12
    cc0
    @0
    c1
    cmin
    co
    #
    cfz
    co
    #
    cvv
    cP
    wf
    #
    @20
    wph
    @24
    @8
    wph
    @9
    @24
    pthd.p
    cvv
    cP
    wrdffz
    syl
    adantr
    @19
    @23
    cvv
    cP
    cR
    @22
    cc0
    cfz
    pthd.r
    oveq2i
    feq2i
    sylibr
    @8
    @21
    wph
    @8
    cR
    @22
    cn0
    pthd.r
    @0
    nnm1nn0
    syl5eqel
    adantl
    cP
    cR
    cvv
    fvinim0ffz
    syl2anc
    mpbir2and
    ex
    syld
    @1
    @5
    @2
    c0
    cin
    c0
    @1
    @4
    c0
    @2
    @1
    @4
    cP
    c0
    cima
    c0
    @1
    @3
    c0
    cP
    @1
    @3
    c1
    cc0
    c1
    cmin
    co
    #
    cfzo
    co
    #
    c0
    @1
    cR
    @25
    c1
    cfzo
    @1
    cR
    @22
    @25
    pthd.r
    @0
    cc0
    c1
    cmin
    oveq1
    syl5eq
    oveq2d
    @25
    c1
    cle
    wbr
    #
    @26
    c0
    wceq
    #
    @27
    cc0
    c1
    c1
    caddc
    co
    #
    cle
    wbr
    cc0
    c2
    @29
    cle
    0le2
    1p1e2
    breqtrri
    cc0
    c1
    c1
    0re
    1re
    1re
    lesubadd2i
    mpbir
    c1
    cz
    wcel
    @25
    cz
    wcel
    #
    @27
    @28
    wb
    1z
    cc0
    cz
    wcel
    @30
    0z
    cc0
    peano2zm
    ax-mp
    c1
    @25
    fzon
    mp2an
    mpbi
    syl6eq
    imaeq2d
    cP
    ima0
    syl6eq
    ineq2d
    @2
    in0
    syl6eq
    pm2.61d2
end
