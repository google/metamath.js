include "csg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "wcel.mm"
include "cin.mm"
include "csubg.mm"
include "eqid.mm"
include "subgsubcl.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "cntzi.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "cgrp.mm"
include "cbs.mm"
include "subgrcl.mm"
include "syl.mm"
include "wss.mm"
include "subgss.mm"
include "grpcl.mm"
include "grpsubsub4.mm"
include "syl13anc.mm"
include "eqeltrrd.mm"
include "3eqtr4d.mm"
include "grppncan.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "eqeltrd.mm"
include "elind.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "wb.mm"
include "grpsubeq0.mm"
include "mpbid.mm"

theorem subgdisj1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  assume subgdisj.p: |- .+ = ( +g ` G )
  assume subgdisj.o: |- .0. = ( 0g ` G )
  assume subgdisj.z: |- Z = ( Cntz ` G )
  assume subgdisj.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume subgdisj.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume subgdisj.i: |- ( ph -> ( T i^i U ) = { .0. } )
  assume subgdisj.s: |- ( ph -> T C_ ( Z ` U ) )
  assume subgdisj.a: |- ( ph -> A e. T )
  assume subgdisj.c: |- ( ph -> C e. T )
  assume subgdisj.b: |- ( ph -> B e. U )
  assume subgdisj.d: |- ( ph -> D e. U )
  assume subgdisj.j: |- ( ph -> ( A .+ B ) = ( C .+ D ) )


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cC
    cG
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    cA
    cC
    wceq
    #
    wph
    @1
    c.0
    csn
    #
    wcel
    @2
    wph
    @1
    cT
    cU
    cin
    @4
    wph
    cT
    cU
    @1
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cA
    cT
    wcel
    cC
    cT
    wcel
    @1
    cT
    wcel
    subgdisj.t
    subgdisj.a
    subgdisj.c
    cT
    cG
    @0
    cA
    cC
    @0
    eqid
    #
    subgsubcl
    syl3anc
    wph
    @1
    cD
    cB
    @0
    co
    #
    cU
    wph
    cA
    cB
    c.pl
    co
    #
    cB
    @0
    co
    #
    cC
    @0
    co
    #
    cC
    cD
    c.pl
    co
    #
    cC
    @0
    co
    #
    cB
    @0
    co
    #
    @1
    @8
    wph
    @9
    cC
    cB
    c.pl
    co
    #
    @0
    co
    #
    @12
    cB
    cC
    c.pl
    co
    #
    @0
    co
    #
    @11
    @14
    wph
    @9
    @12
    @15
    @17
    @0
    subgdisj.j
    wph
    cC
    cU
    cZ
    cfv
    #
    wcel
    #
    cB
    cU
    wcel
    #
    @15
    @17
    wceq
    wph
    cT
    @19
    cC
    subgdisj.s
    subgdisj.c
    sseldd
    #
    subgdisj.b
    c.pl
    cU
    cG
    cC
    cB
    cZ
    subgdisj.p
    subgdisj.z
    cntzi
    syl2anc
    oveq12d
    wph
    cG
    cgrp
    wcel
    #
    @9
    cG
    cbs
    cfv
    #
    wcel
    #
    cB
    @24
    wcel
    #
    cC
    @24
    wcel
    #
    @11
    @16
    wceq
    wph
    @6
    @23
    subgdisj.t
    cT
    cG
    subgrcl
    syl
    #
    wph
    @23
    cA
    @24
    wcel
    #
    @26
    @25
    @28
    wph
    cT
    @24
    cA
    wph
    @6
    cT
    @24
    wss
    subgdisj.t
    @24
    cT
    cG
    @24
    eqid
    #
    subgss
    syl
    #
    subgdisj.a
    sseldd
    #
    wph
    cU
    @24
    cB
    wph
    cU
    @5
    wcel
    #
    cU
    @24
    wss
    subgdisj.u
    @24
    cU
    cG
    @30
    subgss
    syl
    #
    subgdisj.b
    sseldd
    #
    @24
    c.pl
    cG
    cA
    cB
    @30
    subgdisj.p
    grpcl
    syl3anc
    #
    @35
    wph
    cT
    @24
    cC
    @31
    subgdisj.c
    sseldd
    #
    @24
    c.pl
    cG
    @0
    @9
    cB
    cC
    @30
    subgdisj.p
    @7
    grpsubsub4
    syl13anc
    wph
    @23
    @12
    @24
    wcel
    @27
    @26
    @14
    @18
    wceq
    @28
    wph
    @9
    @12
    @24
    subgdisj.j
    @36
    eqeltrrd
    @37
    @35
    @24
    c.pl
    cG
    @0
    @12
    cC
    cB
    @30
    subgdisj.p
    @7
    grpsubsub4
    syl13anc
    3eqtr4d
    wph
    @10
    cA
    cC
    @0
    wph
    @23
    @29
    @26
    @10
    cA
    wceq
    @28
    @32
    @35
    @24
    c.pl
    cG
    @0
    cA
    cB
    @30
    subgdisj.p
    @7
    grppncan
    syl3anc
    oveq1d
    wph
    @13
    cD
    cB
    @0
    wph
    @13
    cD
    cC
    c.pl
    co
    #
    cC
    @0
    co
    #
    cD
    wph
    @12
    @38
    cC
    @0
    wph
    @20
    cD
    cU
    wcel
    #
    @12
    @38
    wceq
    @22
    subgdisj.d
    c.pl
    cU
    cG
    cC
    cD
    cZ
    subgdisj.p
    subgdisj.z
    cntzi
    syl2anc
    oveq1d
    wph
    @23
    cD
    @24
    wcel
    @27
    @39
    cD
    wceq
    @28
    wph
    cU
    @24
    cD
    @34
    subgdisj.d
    sseldd
    @37
    @24
    c.pl
    cG
    @0
    cD
    cC
    @30
    subgdisj.p
    @7
    grppncan
    syl3anc
    eqtrd
    oveq1d
    3eqtr3d
    wph
    @33
    @40
    @21
    @8
    cU
    wcel
    subgdisj.u
    subgdisj.d
    subgdisj.b
    cU
    cG
    @0
    cD
    cB
    @7
    subgsubcl
    syl3anc
    eqeltrd
    elind
    subgdisj.i
    eleqtrd
    @1
    c.0
    elsni
    syl
    wph
    @23
    @29
    @27
    @2
    @3
    wb
    @28
    @32
    @37
    @24
    cG
    @0
    cA
    cC
    c.0
    @30
    subgdisj.o
    @7
    grpsubeq0
    syl3anc
    mpbid
end
