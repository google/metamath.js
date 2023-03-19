include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cioo.mm"
include "covol.mm"
include "ccom.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cmin.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "ovolfcl.mm"
include "ovolioo.mm"
include "syl.mm"
include "cop.mm"
include "cxr.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "ovolfsval.mm"
include "3eqtr4rd.mm"
include "mpteq2dva.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "ovolfsf.mm"
include "feqmptd.mm"
include "id.mm"
include "cpw.mm"
include "ioof.mm"
include "a1i.mm"
include "ffvelrnda.mm"
include "cicc.mm"
include "ovolf.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"

theorem ovolfs2
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  assume ovolfs2.1: |- G = ( ( abs o. - ) o. F )


  assert |- ( F : NN --> ( <_ i^i ( RR X. RR ) ) -> G = ( ( vol* o. (,) ) o. F ) )

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
    #
    vn
    cn
    vn
    cv
    #
    cG
    cfv
    #
    cmpt
    vn
    cn
    @3
    cF
    cfv
    #
    cioo
    cfv
    #
    covol
    cfv
    #
    cmpt
    cG
    covol
    cioo
    ccom
    #
    cF
    ccom
    @2
    vn
    cn
    @4
    @7
    @2
    @3
    cn
    wcel
    wa
    #
    @5
    c1st
    cfv
    #
    @5
    c2nd
    cfv
    #
    cioo
    co
    #
    covol
    cfv
    #
    @11
    @10
    cmin
    co
    #
    @7
    @4
    @9
    @10
    cr
    wcel
    @11
    cr
    wcel
    @10
    @11
    cle
    wbr
    w3a
    @13
    @14
    wceq
    cF
    @3
    ovolfcl
    @10
    @11
    ovolioo
    syl
    @9
    @6
    @12
    covol
    @9
    @6
    @10
    @11
    cop
    #
    cioo
    cfv
    @12
    @9
    @5
    @15
    cioo
    @9
    @5
    cxr
    cxr
    cxp
    #
    wcel
    @5
    @15
    wceq
    @9
    @1
    @16
    @5
    @1
    @0
    @16
    cle
    @0
    inss2
    rexpssxrxp
    sstri
    cn
    @1
    @3
    cF
    ffvelrn
    sseldi
    #
    @5
    cxr
    cxr
    1st2nd2
    syl
    fveq2d
    @10
    @11
    cioo
    df-ov
    syl6eqr
    fveq2d
    cF
    cG
    @3
    ovolfs2.1
    ovolfsval
    3eqtr4rd
    mpteq2dva
    @2
    vn
    cn
    cc0
    cpnf
    cico
    co
    cG
    cF
    cG
    ovolfs2.1
    ovolfsf
    feqmptd
    @2
    vn
    vx
    cn
    @16
    @5
    vx
    cv
    #
    cioo
    cfv
    #
    covol
    cfv
    #
    @7
    cF
    @8
    @17
    @2
    vn
    cn
    @1
    cF
    @2
    id
    feqmptd
    @2
    vx
    vy
    @16
    cr
    cpw
    #
    @19
    vy
    cv
    #
    covol
    cfv
    @20
    cioo
    covol
    @2
    @16
    @21
    @18
    cioo
    @16
    @21
    cioo
    wf
    @2
    ioof
    a1i
    #
    ffvelrnda
    @2
    vx
    @16
    @21
    cioo
    @23
    feqmptd
    @2
    vy
    @21
    cc0
    cpnf
    cicc
    co
    #
    covol
    @21
    @24
    covol
    wf
    @2
    ovolf
    a1i
    feqmptd
    @22
    @19
    covol
    fveq2
    fmptco
    @18
    @5
    wceq
    @19
    @6
    covol
    @18
    @5
    cioo
    fveq2
    fveq2d
    fmptco
    3eqtr4d
end
