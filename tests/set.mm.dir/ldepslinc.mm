include "cv.mm"
include "clindeps.mm"
include "wbr.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "cfsupp.mm"
include "csn.mm"
include "cdif.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "cmap.mm"
include "wrex.mm"
include "wb.mm"
include "cpw.mm"
include "wral.mm"
include "clvec.mm"
include "clmod.mm"
include "wn.mm"
include "wcel.mm"
include "eqid.mm"
include "isldepslvec2.mm"
include "bicomd.mm"
include "rgen2.mm"
include "wo.mm"
include "wne.mm"
include "wi.mm"
include "ldepsnlinc.mm"
include "df-ne.mm"
include "imbi2i.mm"
include "imnan.mm"
include "bitri.mm"
include "ralbii.mm"
include "ralnex.mm"
include "anbi2i.mm"
include "2rexbii.mm"
include "mpbi.mm"
include "orci.mm"
include "r19.43.mm"
include "mpbir.mm"
include "rexbii.mm"
include "xor.mm"
include "bicomi.mm"
include "rexnal.mm"
include "pm3.2i.mm"

theorem ldepslinc
  let vv: setvar v
  let vf: setvar f
  let vm: setvar m
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x

  disjoint f m
  disjoint f s
  disjoint f v
  disjoint m s
  disjoint m v
  disjoint s v
  disjoint k x
  assert |- ( A. m e. LVec A. s e. ~P ( Base ` m ) ( s linDepS m <-> E. v e. s E. f e. ( ( Base ` ( Scalar ` m ) ) ^m ( s \ { v } ) ) ( f finSupp ( 0g ` ( Scalar ` m ) ) /\ ( f ( linC ` m ) ( s \ { v } ) ) = v ) ) /\ -. A. m e. LMod A. s e. ~P ( Base ` m ) ( s linDepS m <-> E. v e. s E. f e. ( ( Base ` ( Scalar ` m ) ) ^m ( s \ { v } ) ) ( f finSupp ( 0g ` ( Scalar ` m ) ) /\ ( f ( linC ` m ) ( s \ { v } ) ) = v ) ) )

  proof
    vs
    cv
    #
    vm
    cv
    #
    clindeps
    wbr
    #
    vf
    cv
    #
    @1
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @3
    @0
    vv
    cv
    #
    csn
    cdif
    #
    @1
    clinc
    cfv
    co
    #
    @7
    wceq
    #
    wa
    #
    vf
    @4
    cbs
    cfv
    #
    @8
    cmap
    co
    #
    wrex
    #
    vv
    @0
    wrex
    #
    wb
    #
    vs
    @1
    cbs
    cfv
    #
    cpw
    #
    wral
    #
    vm
    clvec
    wral
    @19
    vm
    clmod
    wral
    wn
    #
    @16
    vm
    vs
    clvec
    @18
    @1
    clvec
    wcel
    @0
    @18
    wcel
    wa
    @15
    @2
    @17
    @4
    @0
    vf
    @12
    @1
    @5
    @1
    c0g
    cfv
    #
    vv
    @17
    eqid
    @21
    eqid
    @4
    eqid
    @12
    eqid
    @5
    eqid
    isldepslvec2
    bicomd
    rgen2
    @2
    @15
    wn
    #
    wa
    #
    @15
    @2
    wn
    wa
    #
    wo
    #
    vs
    @18
    wrex
    #
    vm
    clmod
    wrex
    #
    @20
    @27
    @23
    vs
    @18
    wrex
    #
    @24
    vs
    @18
    wrex
    #
    wo
    #
    vm
    clmod
    wrex
    #
    @31
    @28
    vm
    clmod
    wrex
    #
    @29
    vm
    clmod
    wrex
    #
    wo
    @32
    @33
    @2
    @6
    @9
    @7
    wne
    #
    wi
    #
    vf
    @13
    wral
    #
    vv
    @0
    wral
    #
    wa
    #
    vs
    @18
    wrex
    vm
    clmod
    wrex
    @32
    vv
    vf
    vm
    vs
    ldepsnlinc
    @38
    @23
    vm
    vs
    clmod
    @18
    @37
    @22
    @2
    @37
    @14
    wn
    #
    vv
    @0
    wral
    @22
    @36
    @39
    vv
    @0
    @36
    @11
    wn
    #
    vf
    @13
    wral
    @39
    @35
    @40
    vf
    @13
    @35
    @6
    @10
    wn
    #
    wi
    @40
    @34
    @41
    @6
    @9
    @7
    df-ne
    imbi2i
    @6
    @10
    imnan
    bitri
    ralbii
    @11
    vf
    @13
    ralnex
    bitri
    ralbii
    @14
    vv
    @0
    ralnex
    bitri
    anbi2i
    2rexbii
    mpbi
    orci
    @28
    @29
    vm
    clmod
    r19.43
    mpbir
    @26
    @30
    vm
    clmod
    @23
    @24
    vs
    @18
    r19.43
    rexbii
    mpbir
    @27
    @19
    wn
    #
    vm
    clmod
    wrex
    @20
    @26
    @42
    vm
    clmod
    @26
    @16
    wn
    #
    vs
    @18
    wrex
    @42
    @25
    @43
    vs
    @18
    @43
    @25
    @2
    @15
    xor
    bicomi
    rexbii
    @16
    vs
    @18
    rexnal
    bitri
    rexbii
    @19
    vm
    clmod
    rexnal
    bitri
    mpbi
    pm3.2i
end
