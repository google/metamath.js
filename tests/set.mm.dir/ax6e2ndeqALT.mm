include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wex.mm"
include "ax6e2nd.mm"
include "wi.mm"
include "ax6e2eq.mm"
include "a1d.mm"
include "exmid.mm"
include "jao.mm"
include "3imp.mm"
include "mp3an.mm"
include "jaoi.mm"
include "wne.mm"
include "hbnae.mm"
include "eximi.mm"
include "nfa1.mm"
include "19.9.mm"
include "sylib.mm"
include "sp.mm"
include "syl.mm"
include "wb.mm"
include "excom.mm"
include "nfn.mm"
include "id.mm"
include "simpr.mm"
include "simpl.mm"
include "pm13.181.mm"
include "ancoms.mm"
include "syl2an2r.mm"
include "neeq2.mm"
include "biimparc.mm"
include "syl2anc.mm"
include "df-ne.mm"
include "bicomi.mm"
include "con3i.mm"
include "sylbir.mm"
include "ex.mm"
include "alrimiv.mm"
include "exim.mm"
include "imbi2.mm"
include "biimpa.mm"
include "sylancr.mm"
include "imbi1.mm"
include "biimpar.mm"
include "pm3.34.mm"
include "orc.mm"
include "imim2i.mm"
include "idiALT.mm"
include "ax-1.mm"
include "olc.mm"
include "exmidne.mm"
include "3imp21.mm"
include "impbii.mm"

theorem ax6e2ndeqALT
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( -. A. x x = y \/ u = v ) <-> E. x E. y ( x = u /\ y = v ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    wal
    #
    wn
    #
    vu
    cv
    #
    vv
    cv
    #
    wceq
    #
    wo
    #
    @0
    @5
    wceq
    #
    @1
    @6
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @4
    @12
    @7
    vx
    vy
    vv
    vu
    ax6e2nd
    #
    @3
    @7
    @12
    wi
    #
    wi
    #
    @4
    @14
    wi
    #
    @3
    @4
    wo
    #
    @14
    vx
    vy
    vv
    vu
    ax6e2eq
    @4
    @12
    @7
    @13
    a1d
    @3
    exmid
    @15
    @16
    @17
    @14
    @3
    @14
    @4
    jao
    3imp
    mp3an
    jaoi
    @5
    @6
    wne
    #
    @12
    @8
    wi
    #
    wi
    #
    @7
    @19
    wi
    #
    @7
    @18
    wo
    #
    @19
    @20
    @18
    @12
    @4
    wi
    #
    @19
    @18
    @4
    vy
    wex
    #
    @4
    wi
    @12
    @24
    wi
    #
    @23
    @24
    @4
    vy
    wal
    #
    @4
    @24
    @26
    vy
    wex
    @26
    @4
    @26
    vy
    vx
    vy
    vy
    hbnae
    eximi
    @26
    vy
    @4
    vy
    nfa1
    19.9
    sylib
    @4
    vy
    sp
    syl
    @18
    @12
    @11
    vx
    wex
    #
    vy
    wex
    #
    wb
    #
    @28
    @24
    wi
    #
    @25
    @11
    vx
    vy
    excom
    @18
    @27
    @4
    wi
    #
    vy
    wal
    @30
    @18
    @31
    vy
    @18
    @4
    vx
    wex
    #
    @4
    wb
    #
    @27
    @32
    wi
    #
    @31
    @4
    vx
    @3
    vx
    @2
    vx
    nfa1
    nfn
    19.9
    @18
    @11
    @4
    wi
    #
    vx
    wal
    @34
    @18
    @35
    vx
    @18
    @11
    @4
    @18
    @11
    wa
    #
    @0
    @1
    wne
    #
    @4
    @36
    @0
    @6
    wne
    #
    @10
    @37
    @18
    @18
    @11
    @9
    @38
    @18
    id
    @36
    @11
    @9
    @18
    @11
    simpr
    #
    @9
    @10
    simpl
    syl
    @9
    @18
    @38
    @0
    @5
    @6
    pm13.181
    ancoms
    syl2an2r
    @36
    @11
    @10
    @39
    @9
    @10
    simpr
    syl
    @10
    @37
    @38
    @1
    @6
    @0
    neeq2
    biimparc
    syl2anc
    @37
    @2
    wn
    #
    @4
    @37
    @40
    @0
    @1
    df-ne
    bicomi
    @3
    @2
    @2
    vx
    sp
    con3i
    sylbir
    syl
    ex
    alrimiv
    @11
    @4
    vx
    exim
    syl
    @33
    @34
    @31
    @32
    @4
    @27
    imbi2
    biimpa
    sylancr
    alrimiv
    @27
    @4
    vy
    exim
    syl
    @29
    @25
    @30
    @12
    @28
    @24
    imbi1
    biimpar
    sylancr
    @12
    @24
    @4
    pm3.34
    sylancr
    @4
    @8
    @12
    @4
    @7
    orc
    imim2i
    syl
    idiALT
    @21
    @7
    @12
    @7
    wi
    #
    @19
    @7
    @7
    @41
    @7
    id
    @7
    @12
    ax-1
    syl
    @7
    @8
    @12
    @7
    @4
    olc
    imim2i
    syl
    idiALT
    @5
    @6
    exmidne
    @21
    @20
    @22
    @19
    @7
    @19
    @18
    jao
    3imp21
    mp3an
    impbii
end
