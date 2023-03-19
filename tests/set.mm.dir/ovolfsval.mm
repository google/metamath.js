include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "c2nd.mm"
include "c1st.mm"
include "co.mm"
include "fveq1i.mm"
include "fvco3.mm"
include "syl5eq.mm"
include "cop.mm"
include "wceq.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "cc.mm"
include "wbr.mm"
include "ovolfcl.mm"
include "simp1d.mm"
include "recnd.mm"
include "simp2d.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "w3a.mm"
include "abssuble0.mm"
include "eqtrd.mm"

theorem ovolfsval
  let cF: class F
  let cG: class G
  let cN: class N
  assume ovolfs.1: |- G = ( ( abs o. - ) o. F )


  assert |- ( ( F : NN --> ( <_ i^i ( RR X. RR ) ) /\ N e. NN ) -> ( G ` N ) = ( ( 2nd ` ( F ` N ) ) - ( 1st ` ( F ` N ) ) ) )

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
    cG
    cfv
    #
    cN
    cF
    cfv
    #
    cabs
    cmin
    ccom
    #
    cfv
    #
    @4
    c2nd
    cfv
    #
    @4
    c1st
    cfv
    #
    cmin
    co
    #
    @2
    @3
    cN
    @5
    cF
    ccom
    #
    cfv
    @6
    cN
    cG
    @10
    ovolfs.1
    fveq1i
    cn
    @1
    cN
    @5
    cF
    fvco3
    syl5eq
    @2
    @6
    @8
    @7
    @5
    co
    #
    @9
    @2
    @6
    @8
    @7
    cop
    #
    @5
    cfv
    @11
    @2
    @4
    @12
    @5
    @2
    @4
    @0
    wcel
    @4
    @12
    wceq
    @2
    @1
    @0
    @4
    cle
    @0
    inss2
    cn
    @1
    cN
    cF
    ffvelrn
    sseldi
    @4
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @8
    @7
    @5
    df-ov
    syl6eqr
    @2
    @11
    @8
    @7
    cmin
    co
    cabs
    cfv
    #
    @9
    @2
    @8
    cc
    wcel
    @7
    cc
    wcel
    @11
    @13
    wceq
    @2
    @8
    @2
    @8
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @8
    @7
    cle
    wbr
    #
    cF
    cN
    ovolfcl
    #
    simp1d
    recnd
    @2
    @7
    @2
    @14
    @15
    @16
    @17
    simp2d
    recnd
    @8
    @7
    @5
    @5
    eqid
    cnmetdval
    syl2anc
    @2
    @14
    @15
    @16
    w3a
    @13
    @9
    wceq
    @17
    @8
    @7
    abssuble0
    syl
    eqtrd
    eqtrd
    eqtrd
end
