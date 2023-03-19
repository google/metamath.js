include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "c1stf.mm"
include "co.mm"
include "ccurf.mm"
include "diagval.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "eqid.mm"
include "cxpc.mm"
include "1stfcl.mm"
include "curf11.mm"
include "df-ov.mm"
include "cxp.mm"
include "chom.mm"
include "xpcbas.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "1stf1.mm"
include "wceq.mm"
include "op1stg.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem diag11
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vd: setvar d
  assume diagval.l: |- L = ( C DiagFunc D )
  assume diagval.c: |- ( ph -> C e. Cat )
  assume diagval.d: |- ( ph -> D e. Cat )
  assume diag11.a: |- A = ( Base ` C )
  assume diag11.c: |- ( ph -> X e. A )
  assume diag11.k: |- K = ( ( 1st ` L ) ` X )
  assume diag11.b: |- B = ( Base ` D )
  assume diag11.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( 1st ` K ) ` Y ) = X )

  proof
    wph
    cY
    cK
    c1st
    cfv
    #
    cfv
    cY
    cX
    cC
    cD
    cop
    cC
    cD
    c1stf
    co
    #
    ccurf
    co
    #
    c1st
    cfv
    #
    cfv
    #
    c1st
    cfv
    #
    cfv
    cX
    cY
    @1
    c1st
    cfv
    #
    co
    #
    cX
    wph
    cY
    @0
    @5
    wph
    cK
    @4
    c1st
    wph
    cK
    cX
    cL
    c1st
    cfv
    #
    cfv
    @4
    diag11.k
    wph
    cX
    @8
    @3
    wph
    cL
    @2
    c1st
    wph
    cC
    cD
    cL
    diagval.l
    diagval.c
    diagval.d
    diagval
    fveq2d
    fveq1d
    syl5eq
    fveq2d
    fveq1d
    wph
    cA
    cB
    cC
    cD
    cC
    @1
    @2
    @4
    cX
    cY
    @2
    eqid
    diag11.a
    diagval.c
    diagval.d
    wph
    cC
    cD
    @1
    cC
    cD
    cxpc
    co
    #
    @9
    eqid
    #
    diagval.c
    diagval.d
    @1
    eqid
    #
    1stfcl
    diag11.b
    diag11.c
    @4
    eqid
    diag11.y
    curf11
    wph
    @7
    cX
    cY
    cop
    #
    c1st
    cfv
    #
    cX
    wph
    @7
    @12
    @6
    cfv
    @13
    cX
    cY
    @6
    df-ov
    wph
    cA
    cB
    cxp
    #
    cC
    cD
    @1
    @12
    @9
    @9
    chom
    cfv
    #
    @10
    cC
    cD
    @9
    cA
    cB
    @10
    diag11.a
    diag11.b
    xpcbas
    @15
    eqid
    diagval.c
    diagval.d
    @11
    wph
    cX
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    @12
    @14
    wcel
    diag11.c
    diag11.y
    cX
    cY
    cA
    cB
    opelxpi
    syl2anc
    1stf1
    syl5eq
    wph
    @16
    @17
    @13
    cX
    wceq
    diag11.c
    diag11.y
    cX
    cY
    cA
    cB
    op1stg
    syl2anc
    eqtrd
    3eqtrd
end
