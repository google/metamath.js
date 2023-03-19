include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "resundi.mm"
include "sseq1i.mm"
include "unss.mm"
include "cop.mm"
include "wcel.mm"
include "weq.mm"
include "wex.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "df-br.mm"
include "vex.mm"
include "ideq.mm"
include "bitr3i.mm"
include "eldm.mm"
include "anbi12i.mm"
include "opelres.mm"
include "19.42v.mm"
include "3bitr4i.mm"
include "bicomi.mm"
include "imbi12i.mm"
include "2albii.mm"
include "19.23v.mm"
include "alcom.mm"
include "ancomst.mm"
include "impexp.mm"
include "bitri.mm"
include "albii.mm"
include "19.21v.mm"
include "equcom.mm"
include "imbi1i.mm"
include "breq2.mm"
include "equsalvw.mm"
include "imbi2i.mm"
include "3bitri.mm"
include "elrn.mm"
include "alrot3.mm"
include "3bitr2i.mm"
include "19.26-2.mm"
include "pm4.76.mm"

theorem undmrnresiss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  assert |- ( ( _I |` ( dom A u. ran A ) ) C_ B <-> A. x A. y ( x A y -> ( x B x /\ y B y ) ) )

  proof
    cid
    cA
    cdm
    #
    cA
    crn
    #
    cun
    cres
    #
    cB
    wss
    cid
    @0
    cres
    #
    cid
    @1
    cres
    #
    cun
    #
    cB
    wss
    @3
    cB
    wss
    #
    @4
    cB
    wss
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    wbr
    #
    @9
    @9
    cB
    wbr
    #
    @10
    @10
    cB
    wbr
    #
    wa
    wi
    #
    vy
    wal
    vx
    wal
    #
    @2
    @5
    cB
    cid
    @0
    @1
    resundi
    sseq1i
    @3
    @4
    cB
    unss
    @8
    @11
    @12
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @11
    @13
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    @16
    @19
    wa
    #
    vy
    wal
    vx
    wal
    @15
    @6
    @18
    @7
    @20
    @6
    @9
    vz
    cv
    #
    cop
    #
    @3
    wcel
    #
    @23
    cB
    wcel
    #
    wi
    #
    vz
    wal
    vx
    wal
    #
    vx
    vz
    weq
    #
    @11
    wa
    #
    vy
    wex
    #
    @9
    @22
    cB
    wbr
    #
    wi
    #
    vz
    wal
    vx
    wal
    #
    @18
    @3
    wrel
    @6
    @27
    wb
    cid
    @0
    relres
    vx
    vz
    @3
    cB
    ssrel
    ax-mp
    @26
    @32
    vx
    vz
    @24
    @30
    @25
    @31
    @23
    cid
    wcel
    #
    @9
    @0
    wcel
    #
    wa
    @28
    @11
    vy
    wex
    #
    wa
    @24
    @30
    @34
    @28
    @35
    @36
    @34
    @9
    @22
    cid
    wbr
    @28
    @9
    @22
    cid
    df-br
    @9
    @22
    vz
    vex
    #
    ideq
    bitr3i
    vy
    @9
    cA
    vx
    vex
    eldm
    anbi12i
    @9
    @22
    cid
    @0
    @37
    opelres
    @28
    @11
    vy
    19.42v
    3bitr4i
    @31
    @25
    @9
    @22
    cB
    df-br
    bicomi
    imbi12i
    2albii
    @33
    @29
    @31
    wi
    #
    vy
    wal
    #
    vz
    wal
    #
    vx
    wal
    @18
    @32
    @39
    vx
    vz
    @39
    @32
    @29
    @31
    vy
    19.23v
    bicomi
    2albii
    @40
    @17
    vx
    @40
    @38
    vz
    wal
    #
    vy
    wal
    @17
    @38
    vz
    vy
    alcom
    @41
    @16
    vy
    @41
    @11
    @28
    @31
    wi
    #
    wi
    #
    vz
    wal
    @11
    @42
    vz
    wal
    #
    wi
    @16
    @38
    @43
    vz
    @38
    @11
    @28
    wa
    @31
    wi
    @43
    @28
    @11
    @31
    ancomst
    @11
    @28
    @31
    impexp
    bitri
    albii
    @11
    @42
    vz
    19.21v
    @44
    @12
    @11
    @44
    vz
    vx
    weq
    #
    @31
    wi
    #
    vz
    wal
    @12
    @42
    @46
    vz
    @28
    @45
    @31
    vx
    vz
    equcom
    imbi1i
    albii
    @31
    @12
    vz
    vx
    @22
    @9
    @9
    cB
    breq2
    equsalvw
    bitri
    imbi2i
    3bitri
    albii
    bitri
    albii
    bitri
    3bitri
    @7
    @10
    @22
    cop
    #
    @4
    wcel
    #
    @47
    cB
    wcel
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    vy
    vz
    weq
    #
    @11
    wa
    #
    vx
    wex
    #
    @10
    @22
    cB
    wbr
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    @20
    @4
    wrel
    @7
    @51
    wb
    cid
    @1
    relres
    vy
    vz
    @4
    cB
    ssrel
    ax-mp
    @50
    @56
    vy
    vz
    @48
    @54
    @49
    @55
    @47
    cid
    wcel
    #
    @10
    @1
    wcel
    #
    wa
    @52
    @11
    vx
    wex
    #
    wa
    @48
    @54
    @58
    @52
    @59
    @60
    @58
    @10
    @22
    cid
    wbr
    @52
    @10
    @22
    cid
    df-br
    @10
    @22
    @37
    ideq
    bitr3i
    vx
    @10
    cA
    vy
    vex
    elrn
    anbi12i
    @10
    @22
    cid
    @1
    @37
    opelres
    @52
    @11
    vx
    19.42v
    3bitr4i
    @55
    @49
    @10
    @22
    cB
    df-br
    bicomi
    imbi12i
    2albii
    @57
    @53
    @55
    wi
    #
    vx
    wal
    #
    vz
    wal
    vy
    wal
    @61
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @20
    @56
    @62
    vy
    vz
    @62
    @56
    @53
    @55
    vx
    19.23v
    bicomi
    2albii
    @61
    vx
    vy
    vz
    alrot3
    @63
    @19
    vx
    vy
    @63
    @11
    @52
    @55
    wi
    #
    wi
    #
    vz
    wal
    @11
    @64
    vz
    wal
    #
    wi
    @19
    @61
    @65
    vz
    @61
    @11
    @52
    wa
    @55
    wi
    @65
    @52
    @11
    @55
    ancomst
    @11
    @52
    @55
    impexp
    bitri
    albii
    @11
    @64
    vz
    19.21v
    @66
    @13
    @11
    @66
    vz
    vy
    weq
    #
    @55
    wi
    #
    vz
    wal
    @13
    @64
    @68
    vz
    @52
    @67
    @55
    vy
    vz
    equcom
    imbi1i
    albii
    @55
    @13
    vz
    vy
    @22
    @10
    @10
    cB
    breq2
    equsalvw
    bitri
    imbi2i
    3bitri
    2albii
    3bitr2i
    3bitri
    anbi12i
    @16
    @19
    vx
    vy
    19.26-2
    @21
    @14
    vx
    vy
    @11
    @12
    @13
    pm4.76
    2albii
    3bitr2i
    3bitr2i
end
