include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "symgbasf.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "fndifnfp.mm"
include "rabfi.mm"
include "adantr.mm"
include "eqeltrd.mm"

theorem sygbasnfpfi
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let vx: setvar x
  assume psgnfvalfi.g: |- G = ( SymGrp ` D )
  assume psgnfvalfi.b: |- B = ( Base ` G )


  assert |- ( ( D e. Fin /\ P e. B ) -> dom ( P \ _I ) e. Fin )

  proof
    cD
    cfn
    wcel
    #
    cP
    cB
    wcel
    #
    wa
    #
    cP
    cid
    cdif
    cdm
    #
    vx
    cv
    #
    cP
    cfv
    @4
    wne
    #
    vx
    cD
    crab
    #
    cfn
    @2
    cP
    cD
    wfn
    #
    @3
    @6
    wceq
    @1
    @7
    @0
    @1
    cD
    cD
    cP
    wf
    @7
    cD
    cB
    cP
    cG
    psgnfvalfi.g
    psgnfvalfi.b
    symgbasf
    cD
    cD
    cP
    ffn
    syl
    adantl
    vx
    cD
    cP
    fndifnfp
    syl
    @0
    @6
    cfn
    wcel
    @1
    @5
    vx
    cD
    rabfi
    adantr
    eqeltrd
end
