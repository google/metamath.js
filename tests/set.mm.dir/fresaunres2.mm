include "wf.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "cdif.mm"
include "wfn.mm"
include "ffn.mm"
include "id.mm"
include "resasplit.mm"
include "syl3an.mm"
include "reseq1d.mm"
include "resundir.mm"
include "wss.mm"
include "inss2.mm"
include "resabs2.mm"
include "ax-mp.mm"
include "uneq12i.mm"
include "c0.mm"
include "cdm.mm"
include "dmres.mm"
include "ineq2i.mm"
include "disjdif.mm"
include "ineq1i.mm"
include "inass.mm"
include "inss1.mm"
include "0ss.mm"
include "eqssi.mm"
include "3eqtr3i.mm"
include "eqtri.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "reldm0.mm"
include "mpbir.mm"
include "difss.mm"
include "uneq2i.mm"
include "simp3.mm"
include "uneq1d.mm"
include "wa.mm"
include "uncom.mm"
include "un0.mm"
include "resundi.mm"
include "incom.mm"
include "uneq1i.mm"
include "inundif.mm"
include "reseq2i.mm"
include "fnresdm.mm"
include "syl.mm"
include "adantl.mm"
include "syl5eq.mm"
include "syl5eqr.mm"
include "3adant3.mm"
include "eqtrd.mm"

theorem fresaunres2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : A --> C /\ G : B --> C /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` B ) = G )

  proof
    cA
    cC
    cF
    wf
    #
    cB
    cC
    cG
    wf
    #
    cF
    cA
    cB
    cin
    #
    cres
    #
    cG
    @2
    cres
    #
    wceq
    #
    w3a
    #
    cF
    cG
    cun
    #
    cB
    cres
    @3
    cF
    cA
    cB
    cdif
    #
    cres
    #
    cG
    cB
    cA
    cdif
    #
    cres
    #
    cun
    #
    cun
    #
    cB
    cres
    #
    cG
    @6
    @7
    @13
    cB
    @0
    cF
    cA
    wfn
    @1
    cG
    cB
    wfn
    #
    @5
    @5
    @7
    @13
    wceq
    cA
    cC
    cF
    ffn
    cB
    cC
    cG
    ffn
    #
    @5
    id
    cA
    cB
    cF
    cG
    resasplit
    syl3an
    reseq1d
    @6
    @14
    @3
    cB
    cres
    #
    @12
    cB
    cres
    #
    cun
    #
    cG
    @3
    @12
    cB
    resundir
    @6
    @19
    @3
    @9
    cB
    cres
    #
    @11
    cB
    cres
    #
    cun
    #
    cun
    #
    cG
    @17
    @3
    @18
    @22
    @2
    cB
    wss
    @17
    @3
    wceq
    cA
    cB
    inss2
    cF
    @2
    cB
    resabs2
    ax-mp
    @9
    @11
    cB
    resundir
    uneq12i
    @6
    @23
    @3
    c0
    @11
    cun
    #
    cun
    #
    cG
    @22
    @24
    @3
    @20
    c0
    @21
    @11
    @20
    c0
    wceq
    #
    @20
    cdm
    #
    c0
    wceq
    #
    @27
    cB
    @9
    cdm
    #
    cin
    #
    c0
    @9
    cB
    dmres
    @30
    cB
    @8
    cF
    cdm
    #
    cin
    #
    cin
    #
    c0
    @29
    @32
    cB
    cF
    @8
    dmres
    ineq2i
    cB
    @8
    cin
    #
    @31
    cin
    c0
    @31
    cin
    #
    @33
    c0
    @34
    c0
    @31
    cB
    cA
    disjdif
    ineq1i
    cB
    @8
    @31
    inass
    @35
    c0
    c0
    @31
    inss1
    @35
    0ss
    eqssi
    3eqtr3i
    eqtri
    eqtri
    @20
    wrel
    @26
    @28
    wb
    @9
    cB
    relres
    @20
    reldm0
    ax-mp
    mpbir
    @10
    cB
    wss
    @21
    @11
    wceq
    cB
    cA
    difss
    cG
    @10
    cB
    resabs2
    ax-mp
    uneq12i
    uneq2i
    @6
    @25
    @4
    @24
    cun
    #
    cG
    @6
    @3
    @4
    @24
    @0
    @1
    @5
    simp3
    uneq1d
    @0
    @1
    @36
    cG
    wceq
    @5
    @0
    @1
    wa
    #
    @36
    @4
    @11
    cun
    #
    cG
    @24
    @11
    @4
    @24
    @11
    c0
    cun
    @11
    c0
    @11
    uncom
    @11
    un0
    eqtri
    uneq2i
    @37
    @38
    cG
    @2
    @10
    cun
    #
    cres
    #
    cG
    cG
    @2
    @10
    resundi
    @37
    @40
    cG
    cB
    cres
    #
    cG
    @39
    cB
    cG
    @39
    cB
    cA
    cin
    #
    @10
    cun
    cB
    @2
    @42
    @10
    cA
    cB
    incom
    uneq1i
    cB
    cA
    inundif
    eqtri
    reseq2i
    @1
    @41
    cG
    wceq
    #
    @0
    @1
    @15
    @43
    @16
    cB
    cG
    fnresdm
    syl
    adantl
    syl5eq
    syl5eqr
    syl5eq
    3adant3
    eqtrd
    syl5eq
    syl5eq
    syl5eq
    eqtrd
end
