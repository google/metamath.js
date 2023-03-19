include "cn.mm"
include "wcel.mm"
include "cphi.mm"
include "cfv.mm"
include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "crab.mm"
include "chash.mm"
include "czrh.mm"
include "cres.mm"
include "ccnv.mm"
include "cima.mm"
include "dfphi2.mm"
include "wa.mm"
include "cab.mm"
include "cbs.mm"
include "wf1o.mm"
include "wfn.mm"
include "wb.mm"
include "cz.mm"
include "cif.mm"
include "cn0.mm"
include "nnnn0.mm"
include "eqid.mm"
include "znf1o.mm"
include "syl.mm"
include "wne.mm"
include "nnne0.mm"
include "ifnefalse.mm"
include "reseq2.mm"
include "f1oeq1.mm"
include "f1oeq2.mm"
include "bitrd.mm"
include "3syl.mm"
include "mpbid.mm"
include "f1ofn.mm"
include "elpreima.mm"
include "fvres.mm"
include "adantl.mm"
include "eleq1d.mm"
include "elfzoelz.mm"
include "znunit.mm"
include "syl2an.mm"
include "pm5.32da.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "cen.mm"
include "wbr.mm"
include "wf1.mm"
include "cvv.mm"
include "wss.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "ovexd.mm"
include "unitss.mm"
include "a1i.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "f1imaen2g.mm"
include "syl22anc.mm"
include "hasheni.mm"
include "3eqtr2rd.mm"

theorem znunithash
  let cU: class U
  let cN: class N
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cE: class E
  let cL: class L
  assume znchr.y: |- Y = ( Z/nZ ` N )
  assume znunit.u: |- U = ( Unit ` Y )


  assert |- ( N e. NN -> ( # ` U ) = ( phi ` N ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cphi
    cfv
    vx
    cv
    #
    cN
    cgcd
    co
    c1
    wceq
    #
    vx
    cc0
    cN
    cfzo
    co
    #
    crab
    #
    chash
    cfv
    cY
    czrh
    cfv
    #
    @3
    cres
    #
    ccnv
    #
    cU
    cima
    #
    chash
    cfv
    #
    cU
    chash
    cfv
    #
    vx
    cN
    dfphi2
    @0
    @8
    @4
    chash
    @0
    @8
    @1
    @3
    wcel
    #
    @2
    wa
    #
    vx
    cab
    @4
    @0
    @12
    vx
    @8
    @0
    @1
    @8
    wcel
    #
    @11
    @1
    @6
    cfv
    #
    cU
    wcel
    #
    wa
    #
    @12
    @0
    @3
    cY
    cbs
    cfv
    #
    @6
    wf1o
    #
    @6
    @3
    wfn
    @13
    @16
    wb
    @0
    cN
    cc0
    wceq
    cz
    @3
    cif
    #
    @17
    @5
    @19
    cres
    #
    wf1o
    #
    @18
    @0
    cN
    cn0
    wcel
    #
    @21
    cN
    nnnn0
    #
    @17
    @20
    cN
    @19
    cY
    znchr.y
    @17
    eqid
    #
    @20
    eqid
    @19
    eqid
    znf1o
    syl
    @0
    cN
    cc0
    wne
    @19
    @3
    wceq
    #
    @21
    @18
    wb
    cN
    nnne0
    cN
    cc0
    cz
    @3
    ifnefalse
    @25
    @21
    @19
    @17
    @6
    wf1o
    #
    @18
    @25
    @20
    @6
    wceq
    @21
    @26
    wb
    @19
    @3
    @5
    reseq2
    @19
    @17
    @20
    @6
    f1oeq1
    syl
    @19
    @3
    @17
    @6
    f1oeq2
    bitrd
    3syl
    mpbid
    #
    @3
    @17
    @6
    f1ofn
    @3
    @1
    cU
    @6
    elpreima
    3syl
    @0
    @11
    @15
    @2
    @0
    @11
    wa
    #
    @15
    @1
    @5
    cfv
    #
    cU
    wcel
    #
    @2
    @28
    @14
    @29
    cU
    @11
    @14
    @29
    wceq
    @0
    @1
    @3
    @5
    fvres
    adantl
    eleq1d
    @0
    @22
    @1
    cz
    wcel
    @30
    @2
    wb
    @11
    @23
    @1
    cc0
    cN
    elfzoelz
    @1
    cU
    @5
    cN
    cY
    znchr.y
    znunit.u
    @5
    eqid
    znunit
    syl2an
    bitrd
    pm5.32da
    bitrd
    abbi2dv
    @2
    vx
    @3
    df-rab
    syl6eqr
    fveq2d
    @0
    @8
    cU
    cen
    wbr
    #
    @9
    @10
    wceq
    @0
    @17
    @3
    @7
    wf1
    #
    @3
    cvv
    wcel
    cU
    @17
    wss
    #
    cU
    cvv
    wcel
    #
    @31
    @0
    @18
    @17
    @3
    @7
    wf1o
    @32
    @27
    @3
    @17
    @6
    f1ocnv
    @17
    @3
    @7
    f1of1
    3syl
    @0
    cc0
    cN
    cfzo
    ovexd
    @33
    @0
    @17
    cY
    cU
    @24
    znunit.u
    unitss
    a1i
    @34
    @0
    cU
    cY
    cui
    cfv
    cvv
    znunit.u
    cY
    cui
    fvex
    eqeltri
    a1i
    @17
    @3
    cU
    @7
    cvv
    f1imaen2g
    syl22anc
    @8
    cU
    hasheni
    syl
    3eqtr2rd
end
