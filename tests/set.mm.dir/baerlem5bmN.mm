include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cminusg.mm"
include "cin.mm"
include "wcel.mm"
include "wceq.mm"
include "eldifad.mm"
include "eqid.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodvnegcl.mm"
include "clss.mm"
include "cpr.mm"
include "lspprcl.mm"
include "lssneln0.mm"
include "wne.mm"
include "lspindpi.mm"
include "simpld.mm"
include "lspsnne1.mm"
include "necomd.mm"
include "lspexchn2.mm"
include "wa.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "adantr.mm"
include "grpinvinv.mm"
include "simpr.mm"
include "lssvnegcl.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "mtand.mm"
include "lspsnneg.mm"
include "neeqtrrd.mm"
include "cdif.mm"
include "grpinvnzcl.mm"
include "baerlem5b.mm"
include "oveq2d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "ineq12d.mm"
include "3eqtrd.mm"

theorem baerlem5bmN
  let wph: wff ph
  let c.pl: class .+
  let c.po: class .(+)
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume baerlem3.v: |- V = ( Base ` W )
  assume baerlem3.m: |- .- = ( -g ` W )
  assume baerlem3.o: |- .0. = ( 0g ` W )
  assume baerlem3.s: |- .(+) = ( LSSum ` W )
  assume baerlem3.n: |- N = ( LSpan ` W )
  assume baerlem3.w: |- ( ph -> W e. LVec )
  assume baerlem3.x: |- ( ph -> X e. V )
  assume baerlem3.c: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume baerlem3.d: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume baerlem3.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume baerlem3.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume baerlem5a.p: |- .+ = ( +g ` W )


  assert |- ( ph -> ( N ` { ( Y .- Z ) } ) = ( ( ( N ` { Y } ) .(+) ( N ` { Z } ) ) i^i ( ( N ` { ( X .- ( Y .- Z ) ) } ) .(+) ( N ` { X } ) ) ) )

  proof
    wph
    cY
    cZ
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    cY
    cZ
    cW
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    csn
    #
    cN
    cfv
    cY
    csn
    cN
    cfv
    #
    @3
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    @4
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cin
    @6
    cZ
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    @0
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @12
    c.po
    co
    #
    cin
    wph
    @1
    @5
    cN
    wph
    @0
    @4
    wph
    cY
    cV
    wcel
    cZ
    cV
    wcel
    #
    @0
    @4
    wceq
    wph
    cY
    cV
    c.0
    csn
    #
    baerlem3.y
    eldifad
    #
    wph
    cZ
    cV
    @21
    baerlem3.z
    eldifad
    #
    cV
    c.pl
    cW
    @2
    c.mi
    cY
    cZ
    baerlem3.v
    baerlem5a.p
    @2
    eqid
    #
    baerlem3.m
    grpsubval
    syl2anc
    #
    sneqd
    fveq2d
    wph
    c.pl
    c.po
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    @3
    baerlem3.v
    baerlem3.m
    baerlem3.o
    baerlem3.s
    baerlem3.n
    baerlem3.w
    baerlem3.x
    wph
    cN
    cV
    cW
    @3
    cX
    cY
    baerlem3.v
    baerlem3.n
    baerlem3.w
    wph
    cW
    clmod
    wcel
    #
    @20
    @3
    cV
    wcel
    wph
    cW
    clvec
    wcel
    @26
    baerlem3.w
    cW
    lveclmod
    syl
    #
    @23
    @2
    cV
    cW
    cZ
    baerlem3.v
    @24
    lmodvnegcl
    syl2anc
    baerlem3.x
    @22
    wph
    cN
    cV
    cW
    cX
    cY
    c.0
    baerlem3.v
    baerlem3.o
    baerlem3.n
    baerlem3.w
    wph
    cW
    clss
    cfv
    #
    cY
    cZ
    cpr
    cN
    cfv
    cV
    cW
    cX
    c.0
    baerlem3.v
    baerlem3.o
    @28
    eqid
    #
    @27
    wph
    @28
    cN
    cV
    cW
    cY
    cZ
    baerlem3.v
    @29
    baerlem3.n
    @27
    @22
    @23
    lspprcl
    baerlem3.x
    baerlem3.c
    lssneln0
    @22
    wph
    @12
    @6
    wne
    @12
    @14
    wne
    wph
    cN
    cV
    cW
    cX
    cY
    cZ
    baerlem3.v
    baerlem3.n
    baerlem3.w
    baerlem3.x
    @22
    @23
    baerlem3.c
    lspindpi
    simpld
    lspsnne1
    wph
    @3
    cY
    cX
    cpr
    cN
    cfv
    #
    wcel
    #
    cZ
    @30
    wcel
    wph
    cN
    cV
    cW
    cX
    cZ
    cY
    baerlem3.v
    baerlem3.n
    baerlem3.w
    baerlem3.x
    @23
    @22
    wph
    cN
    cV
    cW
    cZ
    cY
    c.0
    baerlem3.v
    baerlem3.o
    baerlem3.n
    baerlem3.w
    baerlem3.z
    @22
    wph
    @6
    @14
    baerlem3.d
    necomd
    lspsnne1
    baerlem3.c
    lspexchn2
    wph
    @31
    wa
    #
    @3
    @2
    cfv
    #
    cZ
    @30
    @32
    cW
    cgrp
    wcel
    #
    @20
    @33
    cZ
    wceq
    wph
    @34
    @31
    wph
    @26
    @34
    @27
    cW
    lmodgrp
    syl
    #
    adantr
    wph
    @20
    @31
    @23
    adantr
    cV
    cW
    @2
    cZ
    baerlem3.v
    @24
    grpinvinv
    syl2anc
    @32
    @26
    @30
    @28
    wcel
    #
    @31
    @33
    @30
    wcel
    wph
    @26
    @31
    @27
    adantr
    wph
    @36
    @31
    wph
    @28
    cN
    cV
    cW
    cY
    cX
    baerlem3.v
    @29
    baerlem3.n
    @27
    @22
    baerlem3.x
    lspprcl
    adantr
    wph
    @31
    simpr
    @28
    @30
    @2
    cW
    @3
    @29
    @24
    lssvnegcl
    syl3anc
    eqeltrrd
    mtand
    lspexchn2
    wph
    @6
    @14
    @7
    baerlem3.d
    wph
    @26
    @20
    @7
    @14
    wceq
    @27
    @23
    @2
    cN
    cV
    cW
    cZ
    baerlem3.v
    @24
    baerlem3.n
    lspsnneg
    syl2anc
    #
    neeqtrrd
    baerlem3.y
    wph
    @34
    cZ
    cV
    @21
    cdif
    #
    wcel
    @3
    @38
    wcel
    @35
    baerlem3.z
    cV
    cW
    @2
    cZ
    c.0
    baerlem3.v
    baerlem3.o
    @24
    grpinvnzcl
    syl2anc
    baerlem5a.p
    baerlem5b
    wph
    @8
    @15
    @13
    @19
    wph
    @7
    @14
    @6
    c.po
    @37
    oveq2d
    wph
    @11
    @18
    @12
    c.po
    wph
    @10
    @17
    cN
    wph
    @9
    @16
    wph
    @4
    @0
    cX
    c.mi
    wph
    @0
    @4
    @25
    eqcomd
    oveq2d
    sneqd
    fveq2d
    oveq1d
    ineq12d
    3eqtrd
end
