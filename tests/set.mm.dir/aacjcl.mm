include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wa.mm"
include "ccj.mm"
include "caa.mm"
include "cjcl.mm"
include "adantr.mm"
include "fveq2.mm"
include "cj0.mm"
include "syl6eq.mm"
include "cr.mm"
include "difss.mm"
include "wss.mm"
include "zssre.mm"
include "ax-resscn.mm"
include "plyss.mm"
include "mp2an.mm"
include "sstri.mm"
include "sseli.mm"
include "id.mm"
include "plyrecj.mm"
include "syl2anr.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "reximdva.mm"
include "imp.mm"
include "jca.mm"
include "elaa.mm"
include "3imtr4i.mm"

theorem aacjcl
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R


  assert |- ( A e. AA -> ( * ` A ) e. AA )

  proof
    cA
    cc
    wcel
    #
    cA
    vf
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vf
    cz
    cply
    cfv
    #
    c0p
    csn
    #
    cdif
    #
    wrex
    #
    wa
    #
    cA
    ccj
    cfv
    #
    cc
    wcel
    #
    @9
    @1
    cfv
    #
    cc0
    wceq
    #
    vf
    @6
    wrex
    #
    wa
    cA
    caa
    wcel
    @9
    caa
    wcel
    @8
    @10
    @13
    @0
    @10
    @7
    cA
    cjcl
    adantr
    @0
    @7
    @13
    @0
    @3
    @12
    vf
    @6
    @3
    @2
    ccj
    cfv
    #
    cc0
    wceq
    @0
    @1
    @6
    wcel
    #
    wa
    #
    @12
    @3
    @14
    cc0
    ccj
    cfv
    cc0
    @2
    cc0
    ccj
    fveq2
    cj0
    syl6eq
    @16
    @14
    @11
    cc0
    @15
    @1
    cr
    cply
    cfv
    #
    wcel
    @0
    @14
    @11
    wceq
    @0
    @6
    @17
    @1
    @6
    @4
    @17
    @4
    @5
    difss
    cz
    cr
    wss
    cr
    cc
    wss
    @4
    @17
    wss
    zssre
    ax-resscn
    cz
    cr
    plyss
    mp2an
    sstri
    sseli
    @0
    id
    cA
    @1
    plyrecj
    syl2anr
    eqeq1d
    syl5ib
    reximdva
    imp
    jca
    cA
    vf
    elaa
    @9
    vf
    elaa
    3imtr4i
end
