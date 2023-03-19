include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "covol.mm"
include "cfv.mm"
include "cv.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "crab.mm"
include "cinf.mm"
include "simpr.mm"
include "cpw.mm"
include "ioof.mm"
include "simpl.mm"
include "inss2.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "fco.mm"
include "sylancr.mm"
include "frn.mm"
include "syl.mm"
include "sspwuni.mm"
include "sylib.mm"
include "sstrd.mm"
include "eqid.mm"
include "ovolval.mm"
include "wcel.mm"
include "wbr.mm"
include "ssrab2.mm"
include "elovolmr.mm"
include "infxrlb.mm"
include "eqbrtrd.mm"

theorem ovollb
  let cA: class A
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cB: class B
  let wph: wff ph
  let cT: class T
  assume ovollb.1: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )


  assert |- ( ( F : NN --> ( <_ i^i ( RR X. RR ) ) /\ A C_ U. ran ( (,) o. F ) ) -> ( vol* ` A ) <_ sup ( ran S , RR* , < ) )

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
    cA
    cioo
    cF
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    wa
    #
    cA
    covol
    cfv
    #
    cA
    cioo
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    vy
    cv
    caddc
    cabs
    cmin
    ccom
    @9
    ccom
    c1
    cseq
    crn
    cxr
    clt
    csup
    wceq
    wa
    vf
    @1
    cn
    cmap
    co
    wrex
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cS
    crn
    cxr
    clt
    csup
    #
    cle
    @7
    cA
    cr
    wss
    @8
    @12
    wceq
    @7
    cA
    @5
    cr
    @2
    @6
    simpr
    @7
    @4
    cr
    cpw
    #
    wss
    #
    @5
    cr
    wss
    @7
    cn
    @14
    @3
    wf
    #
    @15
    @7
    cxr
    cxr
    cxp
    #
    @14
    cioo
    wf
    cn
    @17
    cF
    wf
    #
    @16
    ioof
    @7
    @2
    @1
    @17
    wss
    @18
    @2
    @6
    simpl
    @1
    @0
    @17
    cle
    @0
    inss2
    rexpssxrxp
    sstri
    cn
    @1
    @17
    cF
    fss
    sylancl
    cn
    @17
    @14
    cioo
    cF
    fco
    sylancr
    cn
    @14
    @3
    frn
    syl
    @4
    cr
    sspwuni
    sylib
    sstrd
    vy
    cA
    vf
    @11
    @11
    eqid
    #
    ovolval
    syl
    @7
    @11
    cxr
    wss
    @13
    @11
    wcel
    @12
    @13
    cle
    wbr
    @10
    vy
    cxr
    ssrab2
    vy
    cA
    cS
    vf
    cF
    @11
    @19
    ovollb.1
    elovolmr
    @11
    @13
    infxrlb
    sylancr
    eqbrtrd
end
