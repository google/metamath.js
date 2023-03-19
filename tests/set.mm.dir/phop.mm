include "ccphlo.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wrel.mm"
include "wceq.mm"
include "phrel.mm"
include "1st2nd.mm"
include "mpan.mm"
include "nmcvfval.mm"
include "opeq2i.mm"
include "cnv.mm"
include "cvc.mm"
include "phnv.mm"
include "eqid.mm"
include "nvvc.mm"
include "vcrel.mm"
include "vafval.mm"
include "smfval.mm"
include "opeq12i.mm"
include "syl6eqr.mm"
include "3syl.mm"
include "opeq1d.mm"
include "syl5eqr.mm"
include "eqtrd.mm"

theorem phop
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  assume phop.2: |- G = ( +v ` U )
  assume phop.4: |- S = ( .sOLD ` U )
  assume phop.6: |- N = ( normCV ` U )


  assert |- ( U e. CPreHilOLD -> U = <. <. G , S >. , N >. )

  proof
    cU
    ccphlo
    wcel
    #
    cU
    cU
    c1st
    cfv
    #
    cU
    c2nd
    cfv
    #
    cop
    #
    cG
    cS
    cop
    #
    cN
    cop
    #
    ccphlo
    wrel
    @0
    cU
    @3
    wceq
    phrel
    cU
    ccphlo
    1st2nd
    mpan
    @0
    @3
    @1
    cN
    cop
    @5
    cN
    @2
    @1
    cU
    cN
    phop.6
    nmcvfval
    opeq2i
    @0
    @1
    @4
    cN
    @0
    cU
    cnv
    wcel
    @1
    cvc
    wcel
    #
    @1
    @4
    wceq
    cU
    phnv
    cU
    @1
    @1
    eqid
    nvvc
    @6
    @1
    @1
    c1st
    cfv
    #
    @1
    c2nd
    cfv
    #
    cop
    #
    @4
    cvc
    wrel
    @6
    @1
    @9
    wceq
    vcrel
    @1
    cvc
    1st2nd
    mpan
    cG
    @7
    cS
    @8
    cU
    cG
    phop.2
    vafval
    cS
    cU
    phop.4
    smfval
    opeq12i
    syl6eqr
    3syl
    opeq1d
    syl5eqr
    eqtrd
end
