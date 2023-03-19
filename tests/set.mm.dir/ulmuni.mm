include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "ulmcl.mm"
include "adantr.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "cv.mm"
include "wcel.mm"
include "cuz.mm"
include "cmap.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "cmpt.mm"
include "cli.mm"
include "cvv.mm"
include "eqid.mm"
include "simplr.mm"
include "simpr.mm"
include "simpllr.mm"
include "fvex.mm"
include "mptex.mm"
include "a1i.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "simp-4l.mm"
include "ulmclm.mm"
include "simp-4r.mm"
include "climuni.mm"
include "syl2anc.mm"
include "wrex.mm"
include "ulmf.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "eqfnfvd.mm"

theorem ulmuni
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let vi: setvar i
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F ( ~~>u ` S ) G /\ F ( ~~>u ` S ) H ) -> G = H )

  proof
    cF
    cG
    cS
    culm
    cfv
    #
    wbr
    #
    cF
    cH
    @0
    wbr
    #
    wa
    #
    vx
    cS
    cG
    cH
    @3
    cS
    cc
    cG
    wf
    #
    cG
    cS
    wfn
    @1
    @4
    @2
    cS
    cF
    cG
    ulmcl
    adantr
    cS
    cc
    cG
    ffn
    syl
    @3
    cS
    cc
    cH
    wf
    #
    cH
    cS
    wfn
    @2
    @5
    @1
    cS
    cF
    cH
    ulmcl
    adantl
    cS
    cc
    cH
    ffn
    syl
    @3
    vx
    cv
    #
    cS
    wcel
    #
    wa
    #
    vn
    cv
    #
    cuz
    cfv
    #
    cc
    cS
    cmap
    co
    cF
    wf
    #
    @6
    cG
    cfv
    #
    @6
    cH
    cfv
    #
    wceq
    #
    vn
    cz
    @8
    @9
    cz
    wcel
    #
    wa
    #
    @11
    wa
    #
    vi
    @10
    @6
    vi
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    @12
    cli
    wbr
    @21
    @13
    cli
    wbr
    @14
    @17
    @6
    cS
    vk
    cF
    cG
    @21
    @9
    cvv
    @10
    @10
    eqid
    #
    @8
    @15
    @11
    simplr
    #
    @16
    @11
    simpr
    #
    @3
    @7
    @15
    @11
    simpllr
    #
    @21
    cvv
    wcel
    @17
    vi
    @10
    @20
    @9
    cuz
    fvex
    mptex
    a1i
    #
    vk
    cv
    #
    @10
    wcel
    #
    @6
    @27
    cF
    cfv
    #
    cfv
    #
    @27
    @21
    cfv
    #
    wceq
    @17
    @28
    @31
    @30
    vi
    @27
    @20
    @30
    @10
    @21
    @18
    @27
    wceq
    @6
    @19
    @29
    @18
    @27
    cF
    fveq2
    fveq1d
    @21
    eqid
    @6
    @29
    fvex
    fvmpt
    eqcomd
    adantl
    #
    @1
    @2
    @7
    @15
    @11
    simp-4l
    ulmclm
    @17
    @6
    cS
    vk
    cF
    cH
    @21
    @9
    cvv
    @10
    @22
    @23
    @24
    @25
    @26
    @32
    @1
    @2
    @7
    @15
    @11
    simp-4r
    ulmclm
    @12
    @13
    @21
    climuni
    syl2anc
    @1
    @11
    vn
    cz
    wrex
    @2
    @7
    cS
    vn
    cF
    cG
    ulmf
    ad2antrr
    r19.29a
    eqfnfvd
end
