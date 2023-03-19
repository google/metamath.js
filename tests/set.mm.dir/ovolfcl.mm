include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "ancom.mm"
include "elin.mm"
include "df-br.mm"
include "bicomi.mm"
include "opelxp.mm"
include "anbi12i.mm"
include "bitri.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "sylib.mm"

theorem ovolfcl
  let cF: class F
  let cN: class N


  assert |- ( ( F : NN --> ( <_ i^i ( RR X. RR ) ) /\ N e. NN ) -> ( ( 1st ` ( F ` N ) ) e. RR /\ ( 2nd ` ( F ` N ) ) e. RR /\ ( 1st ` ( F ` N ) ) <_ ( 2nd ` ( F ` N ) ) ) )

  proof
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    cN
    cn
    wcel
    wa
    #
    cN
    cF
    cfv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cop
    #
    @1
    wcel
    #
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @4
    @5
    cle
    wbr
    #
    w3a
    #
    @2
    @3
    @6
    @1
    @2
    @3
    @0
    wcel
    @3
    @6
    wceq
    @2
    @1
    @0
    @3
    cle
    @0
    inss2
    cn
    @1
    cN
    cF
    ffvelrn
    #
    sseldi
    @3
    cr
    cr
    1st2nd2
    syl
    @12
    eqeltrrd
    @10
    @8
    @9
    wa
    #
    wa
    #
    @13
    @10
    wa
    @7
    @11
    @10
    @13
    ancom
    @7
    @6
    cle
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    @14
    @6
    cle
    @0
    elin
    @15
    @10
    @16
    @13
    @10
    @15
    @4
    @5
    cle
    df-br
    bicomi
    @4
    @5
    cr
    cr
    opelxp
    anbi12i
    bitri
    @8
    @9
    @10
    df-3an
    3bitr4i
    sylib
end
