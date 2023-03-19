include "cur.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmarrep.mm"
include "cminmar1.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "minmar1marrep.mm"
include "syl2anc.mm"
include "oveqd.mm"
include "syl5eq.mm"
include "cbs.mm"
include "ringidcl.mm"
include "syl.mm"
include "marrepcl.mm"
include "syl32anc.mm"
include "eqeltrd.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "w3a.mm"
include "c0g.mm"
include "cif.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "eldifad.mm"
include "simp3.mm"
include "marrepeval.mm"
include "syl222anc.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "3eqtrrd.mm"
include "submateq.mm"

theorem submatminr1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume submateq.a: |- A = ( ( 1 ... N ) Mat R )
  assume submateq.b: |- B = ( Base ` A )
  assume submateq.n: |- ( ph -> N e. NN )
  assume submateq.i: |- ( ph -> I e. ( 1 ... N ) )
  assume submateq.j: |- ( ph -> J e. ( 1 ... N ) )
  assume submatminr1.r: |- ( ph -> R e. Ring )
  assume submatminr1.m: |- ( ph -> M e. B )
  assume submatminr1.e: |- E = ( I ( ( ( 1 ... N ) minMatR1 R ) ` M ) J )


  assert |- ( ph -> ( I ( subMat1 ` M ) J ) = ( I ( subMat1 ` E ) J ) )

  proof
    wph
    cA
    cB
    cR
    vi
    vj
    cM
    cE
    cI
    cJ
    cN
    submateq.a
    submateq.b
    submateq.n
    submateq.i
    submateq.j
    submatminr1.m
    wph
    cE
    cI
    cJ
    cM
    cR
    cur
    cfv
    #
    c1
    cN
    cfz
    co
    #
    cR
    cmarrep
    co
    #
    co
    #
    co
    #
    cB
    wph
    cE
    cI
    cJ
    cM
    @1
    cR
    cminmar1
    co
    cfv
    #
    co
    @4
    submatminr1.e
    wph
    @5
    @3
    cI
    cJ
    wph
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    @5
    @3
    wceq
    submatminr1.r
    submatminr1.m
    cA
    cB
    @2
    cR
    @0
    cM
    @1
    submateq.a
    submateq.b
    @2
    eqid
    #
    @0
    eqid
    #
    minmar1marrep
    syl2anc
    oveqd
    syl5eq
    #
    wph
    @6
    @7
    @0
    cR
    cbs
    cfv
    #
    wcel
    #
    cI
    @1
    wcel
    #
    cJ
    @1
    wcel
    #
    @4
    cB
    wcel
    submatminr1.r
    submatminr1.m
    wph
    @6
    @12
    submatminr1.r
    @11
    cR
    @0
    @11
    eqid
    @9
    ringidcl
    syl
    #
    submateq.i
    submateq.j
    cA
    cB
    cR
    @0
    cI
    cJ
    cM
    @1
    submateq.a
    submateq.b
    marrepcl
    syl32anc
    eqeltrd
    wph
    vi
    cv
    #
    @1
    cI
    csn
    #
    cdif
    wcel
    #
    vj
    cv
    #
    @1
    cJ
    csn
    #
    cdif
    wcel
    #
    w3a
    #
    @16
    @19
    cE
    co
    @16
    @19
    @4
    co
    #
    @16
    cI
    wceq
    #
    @19
    cJ
    wceq
    @0
    cR
    c0g
    cfv
    #
    cif
    #
    @16
    @19
    cM
    co
    #
    cif
    #
    @27
    @22
    cE
    @4
    @16
    @19
    wph
    @18
    cE
    @4
    wceq
    @21
    @10
    3ad2ant1
    oveqd
    @22
    @7
    @12
    @13
    @14
    @16
    @1
    wcel
    #
    @19
    @1
    wcel
    @23
    @28
    wceq
    wph
    @18
    @7
    @21
    submatminr1.m
    3ad2ant1
    wph
    @18
    @12
    @21
    @15
    3ad2ant1
    wph
    @18
    @13
    @21
    submateq.i
    3ad2ant1
    wph
    @18
    @14
    @21
    submateq.j
    3ad2ant1
    @22
    @16
    @1
    @17
    wph
    @18
    @21
    simp2
    #
    eldifad
    @22
    @19
    @1
    @20
    wph
    @18
    @21
    simp3
    eldifad
    cA
    cB
    @2
    cR
    @0
    @16
    @19
    cI
    cJ
    cM
    @1
    @25
    submateq.a
    submateq.b
    @8
    @25
    eqid
    marrepeval
    syl222anc
    @22
    @24
    @26
    @27
    @22
    @16
    cI
    @22
    @29
    @16
    cI
    wne
    #
    @22
    @18
    @29
    @31
    wa
    @30
    @16
    @1
    cI
    eldifsn
    sylib
    simprd
    neneqd
    iffalsed
    3eqtrrd
    submateq
end
