include "cdif.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ntrclsiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ntrclsrcomplex.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "rcompleq.mm"
include "syl2anc.mm"
include "ntrclsnvobr.mm"
include "ntrclsfv.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem ntrclsfveq2
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
  disjoint I j
  disjoint I k
  disjoint S j
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> ( ( I ` ( B \ S ) ) = C <-> ( K ` S ) = ( B \ C ) ) )

  proof
    wph
    cB
    cS
    cdif
    #
    cI
    cfv
    #
    cC
    wceq
    #
    cB
    @1
    cdif
    #
    cB
    cC
    cdif
    #
    wceq
    #
    cS
    cK
    cfv
    #
    @4
    wceq
    wph
    @1
    cB
    wss
    cC
    cB
    wss
    @2
    @5
    wb
    wph
    @1
    cB
    wph
    cB
    cpw
    #
    @7
    @0
    cI
    wph
    cI
    @7
    @7
    cmap
    co
    wcel
    @7
    @7
    cI
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
    ntrclsiex
    cI
    @7
    @7
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
    cC
    cB
    ntrclsfv.c
    elpwid
    @1
    cC
    cB
    rcompleq
    syl2anc
    wph
    @6
    @3
    @4
    wph
    cB
    cD
    cS
    vi
    vj
    vk
    cK
    cI
    cO
    ntrcls.o
    ntrcls.d
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
    ntrclsnvobr
    ntrclsfv.s
    ntrclsfv
    eqeq1d
    bitr4d
end
