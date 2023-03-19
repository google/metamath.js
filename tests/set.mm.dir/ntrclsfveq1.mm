include "cdif.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "elpwid.mm"
include "dfss4.mm"
include "sylib.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "ntrclsfv.mm"
include "eqeq1d.mm"
include "wb.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ntrclskex.mm"
include "elmapi.mm"
include "syl.mm"
include "ntrclsrcomplex.mm"
include "ffvelrnd.mm"
include "difssd.mm"
include "rcompleq.mm"
include "syl2anc.mm"
include "3bitr4d.mm"

theorem ntrclsfveq1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )
  assume ntrclsfv.s: |- ( ph -> S e. ~P B )
  assume ntrclsfv.c: |- ( ph -> C e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint K j
  disjoint K k
  disjoint S j
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( ( I ` S ) = C <-> ( K ` ( B \ S ) ) = ( B \ C ) ) )

  proof
    wph
    cB
    cB
    cS
    cdif
    #
    cK
    cfv
    #
    cdif
    #
    cC
    wceq
    @2
    cB
    cB
    cC
    cdif
    #
    cdif
    #
    wceq
    #
    cS
    cI
    cfv
    #
    cC
    wceq
    @1
    @3
    wceq
    #
    wph
    cC
    @4
    @2
    wph
    @4
    cC
    wph
    cC
    cB
    wss
    @4
    cC
    wceq
    wph
    cC
    cB
    ntrclsfv.c
    elpwid
    cC
    cB
    dfss4
    sylib
    eqcomd
    eqeq2d
    wph
    @6
    @2
    cC
    wph
    cB
    cD
    cS
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclsfv.s
    ntrclsfv
    eqeq1d
    wph
    @1
    cB
    wss
    @3
    cB
    wss
    @7
    @5
    wb
    wph
    @1
    cB
    wph
    cB
    cpw
    #
    @8
    @0
    cK
    wph
    cK
    @8
    @8
    cmap
    co
    wcel
    @8
    @8
    cK
    wf
    wph
    cB
    cD
    vi
    vj
    vk
    cI
    cK
    cO
    ntrcls.o
    ntrcls.d
    ntrcls.r
    ntrclskex
    cK
    @8
    @8
    elmapi
    syl
    wph
    cB
    cD
    cS
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    ffvelrnd
    elpwid
    wph
    cB
    cC
    difssd
    @1
    @3
    cB
    rcompleq
    syl2anc
    3bitr4d
end
