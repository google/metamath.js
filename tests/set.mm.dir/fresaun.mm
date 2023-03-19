include "wf.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cdif.mm"
include "cun.mm"
include "c0.mm"
include "wss.mm"
include "simp1.mm"
include "inss1.mm"
include "fssres.mm"
include "sylancl.mm"
include "difss.mm"
include "simp2.mm"
include "indifdir.mm"
include "disjdif.mm"
include "difeq1i.mm"
include "0dif.mm"
include "3eqtri.mm"
include "a1i.mm"
include "fun2.mm"
include "syl21anc.mm"
include "indi.mm"
include "inass.mm"
include "ineq2i.mm"
include "in0.mm"
include "incom.mm"
include "ineq1i.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "un0.mm"
include "wfn.mm"
include "ffn.mm"
include "id.mm"
include "resasplit.mm"
include "syl3an.mm"
include "feq1d.mm"
include "un12.mm"
include "uneq1i.mm"
include "inundif.mm"
include "uneq2i.mm"
include "undif1.mm"
include "feq2i.mm"
include "syl6rbbr.mm"
include "mpbid.mm"

theorem fresaun
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : A --> C /\ G : B --> C /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( F u. G ) : ( A u. B ) --> C )

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
    wceq
    #
    w3a
    #
    @2
    cA
    cB
    cdif
    #
    cB
    cA
    cdif
    #
    cun
    #
    cun
    #
    cC
    @3
    cF
    @6
    cres
    #
    cG
    @7
    cres
    #
    cun
    #
    cun
    #
    wf
    #
    cA
    cB
    cun
    #
    cC
    cF
    cG
    cun
    #
    wf
    #
    @5
    @2
    cC
    @3
    wf
    #
    @8
    cC
    @12
    wf
    #
    @2
    @8
    cin
    #
    c0
    wceq
    #
    @14
    @5
    @0
    @2
    cA
    wss
    @18
    @0
    @1
    @4
    simp1
    #
    cA
    cB
    inss1
    cA
    cC
    @2
    cF
    fssres
    sylancl
    @5
    @6
    cC
    @10
    wf
    #
    @7
    cC
    @11
    wf
    #
    @6
    @7
    cin
    #
    c0
    wceq
    #
    @19
    @5
    @0
    @6
    cA
    wss
    @23
    @22
    cA
    cB
    difss
    cA
    cC
    @6
    cF
    fssres
    sylancl
    @5
    @1
    @7
    cB
    wss
    @24
    @0
    @1
    @4
    simp2
    cB
    cA
    difss
    cB
    cC
    @7
    cG
    fssres
    sylancl
    @26
    @5
    @25
    cA
    @7
    cin
    #
    cB
    @7
    cin
    #
    cdif
    c0
    @28
    cdif
    c0
    cA
    cB
    @7
    indifdir
    @27
    c0
    @28
    cA
    cB
    disjdif
    #
    difeq1i
    @28
    0dif
    3eqtri
    a1i
    @6
    @7
    cC
    @10
    @11
    fun2
    syl21anc
    @21
    @5
    @20
    @2
    @6
    cin
    #
    @2
    @7
    cin
    #
    cun
    c0
    c0
    cun
    c0
    @2
    @6
    @7
    indi
    @30
    c0
    @31
    c0
    @30
    cA
    cB
    @6
    cin
    #
    cin
    cA
    c0
    cin
    c0
    cA
    cB
    @6
    inass
    @32
    c0
    cA
    cB
    cA
    disjdif
    ineq2i
    cA
    in0
    3eqtri
    @31
    cB
    cA
    cin
    #
    @7
    cin
    #
    c0
    @2
    @33
    @7
    cA
    cB
    incom
    #
    ineq1i
    @34
    cB
    @27
    cin
    cB
    c0
    cin
    c0
    cB
    cA
    @7
    inass
    @27
    c0
    cB
    @29
    ineq2i
    cB
    in0
    3eqtri
    eqtri
    uneq12i
    c0
    un0
    3eqtri
    a1i
    @2
    @8
    cC
    @3
    @12
    fun2
    syl21anc
    @5
    @17
    @15
    cC
    @13
    wf
    @14
    @5
    @15
    cC
    @16
    @13
    @0
    cF
    cA
    wfn
    @1
    cG
    cB
    wfn
    @4
    @4
    @16
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
    @4
    id
    cA
    cB
    cF
    cG
    resasplit
    syl3an
    feq1d
    @9
    @15
    cC
    @13
    @9
    @6
    @2
    @7
    cun
    #
    cun
    @6
    cB
    cun
    @15
    @2
    @6
    @7
    un12
    @36
    cB
    @6
    @36
    @33
    @7
    cun
    cB
    @2
    @33
    @7
    @35
    uneq1i
    cB
    cA
    inundif
    eqtri
    uneq2i
    cA
    cB
    undif1
    3eqtri
    feq2i
    syl6rbbr
    mpbid
end
